#!/usr/bin/env python3
"""Vectorize the hand-drawn book figures into polished, consistent SVGs.

Every figure in book/figures was drawn in the same app on the same canvas
color (245,244,240) with a small set of ink colors. This script:

  1. detects embedded code-editor screenshots (near-white panes) and keeps
     them as high-resolution raster regions embedded in the SVG,
  2. classifies every remaining ink pixel into a canonical palette
     (amber, black, red, orange, green, blue), so ink colors are identical
     across all figures,
  3. traces each ink layer with vtracer into smooth vector paths that
     preserve the handwritten strokes,
  4. crops every figure to its content with a uniform margin and puts it
     on a clean white background.

Usage: python3 vectorize.py [figure.png ...]   (default: all figures)
Output: book/figures-svg/<name>.svg
"""

import base64
import colorsys
import io
import os
import re
import sys
import tempfile

import numpy as np
import vtracer
from PIL import Image
from scipy import ndimage

FIGURES = os.path.join(os.path.dirname(__file__), "..", "figures")
OUTPUT = os.path.join(os.path.dirname(__file__), "..", "figures-svg")

CANVAS = np.array([245, 244, 240])  # shared background of all figures

# Canonical ink palette, chosen as the modal color of each ink cluster
# measured across all 51 figures.
PALETTE = {
    "black": "#141414",
    "amber": "#f0a818",
    "red": "#d84808",
    "orange": "#f87008",
    "green": "#30c858",
    "blue": "#285098",
}

MIN_INK_PIXELS = 400  # ignore ink layers smaller than this (noise)
PANE_MIN_AREA = 0.002  # panes smaller than 0.2% of the image are noise
MARGIN = 0.03  # uniform content margin, fraction of the longer side


def detect_panes(rgb):
    """Bounding boxes of embedded screenshots: connected near-white regions."""
    near_white = rgb.min(axis=2) >= 248
    near_white = ndimage.binary_closing(near_white, np.ones((5, 5)))
    labels, n = ndimage.label(near_white)
    boxes = []
    for sl in ndimage.find_objects(labels):
        if sl is None:
            continue
        h = sl[0].stop - sl[0].start
        w = sl[1].stop - sl[1].start
        if h * w >= PANE_MIN_AREA * rgb.shape[0] * rgb.shape[1]:
            boxes.append([sl[0].start, sl[0].stop, sl[1].start, sl[1].stop])
    return merge_boxes(boxes)


def merge_boxes(boxes, gap=12):
    """Merge overlapping or nearly touching boxes until stable."""
    merged = True
    while merged:
        merged = False
        out = []
        for b in boxes:
            for o in out:
                if (b[0] < o[1] + gap and o[0] < b[1] + gap and
                        b[2] < o[3] + gap and o[2] < b[3] + gap):
                    o[0], o[1] = min(o[0], b[0]), max(o[1], b[1])
                    o[2], o[3] = min(o[2], b[2]), max(o[3], b[3])
                    merged = True
                    break
            else:
                out.append(list(b))
        boxes = out
    return boxes


def classify_ink(rgb, pane_mask):
    """Map every ink pixel to a canonical palette color."""
    diff = np.abs(rgb.astype(int) - CANVAS).sum(axis=2)
    ink = (diff >= 60) & ~pane_mask & ~(rgb.min(axis=2) >= 244)

    r, g, b = [rgb[..., i].astype(float) / 255 for i in range(3)]
    mx, mn = np.maximum(np.maximum(r, g), b), np.minimum(np.minimum(r, g), b)
    v = mx
    s = np.where(mx > 0, (mx - mn) / np.where(mx > 0, mx, 1), 0)
    # hue in degrees
    h = np.zeros_like(mx)
    d = np.where(mx - mn > 0, mx - mn, 1)
    h = np.where(mx == r, (g - b) / d % 6, h)
    h = np.where(mx == g, (b - r) / d + 2, h)
    h = np.where(mx == b, (r - g) / d + 4, h)
    h *= 60

    layers = {}
    grayish = s < 0.30
    layers["black"] = ink & grayish & (v < 0.75)
    chroma = ink & ~grayish
    layers["red"] = chroma & (h < 22)
    layers["orange"] = chroma & (h >= 22) & (h < 38)
    layers["amber"] = chroma & (h >= 38) & (h < 95)
    layers["green"] = chroma & (h >= 95) & (h < 180)
    layers["blue"] = chroma & (h >= 180) & (h < 300)
    return {k: m for k, m in layers.items() if m.sum() >= MIN_INK_PIXELS}


PATH_RE = re.compile(r'<path\s+d="([^"]+)"(?:\s+fill="[^"]*")?'
                     r'(?:\s+transform="([^"]*)")?\s*/?>')


def trace_layer(mask):
    """Trace a binary ink mask into SVG path data with vtracer.

    The mask is traced at 2x resolution: thin strokes trace much more
    faithfully (no spline overshoot), and the caller compensates with a
    scale(0.5) group transform.
    """
    up = Image.fromarray(mask.astype(np.uint8) * 255).resize(
        (mask.shape[1] * 2, mask.shape[0] * 2), Image.LANCZOS)
    a = np.asarray(up) > 127
    img = np.full(a.shape + (3,), 255, dtype=np.uint8)
    img[a] = (0, 0, 0)
    with tempfile.TemporaryDirectory() as tmp:
        src = os.path.join(tmp, "layer.png")
        dst = os.path.join(tmp, "layer.svg")
        Image.fromarray(img, "RGB").save(src)
        vtracer.convert_image_to_svg_py(
            src, dst,
            colormode="binary",
            hierarchical="stacked",
            mode="spline",
            filter_speckle=4,
            corner_threshold=60,
            length_threshold=4.0,
            splice_threshold=45,
            path_precision=1,
        )
        with open(dst) as f:
            svg = f.read()
    return PATH_RE.findall(svg)


def embed_pane(rgb, box):
    """Crop a screenshot pane and return it as a base64 PNG <image> element.

    Canvas-colored pixels inside the crop are remapped to white so that
    embedded panes blend with the normalized white background.
    """
    y0, y1, x0, x1 = box
    region = rgb[y0:y1, x0:x1].copy()
    canvas = np.abs(region.astype(int) - CANVAS).sum(axis=2) <= 16
    region[canvas] = 255
    crop = Image.fromarray(region)
    buf = io.BytesIO()
    crop.save(buf, "PNG", optimize=True)
    data = base64.b64encode(buf.getvalue()).decode()
    return (f'<image x="{x0}" y="{y0}" width="{x1 - x0}" height="{y1 - y0}" '
            f'href="data:image/png;base64,{data}"/>')


def content_bbox(layers, panes, shape):
    """Bounding box of all ink and panes plus a uniform margin."""
    mask = np.zeros(shape[:2], bool)
    for m in layers.values():
        mask |= m
    ys, xs = np.nonzero(mask)
    y0 = min([b[0] for b in panes] + ([ys.min()] if len(ys) else []))
    y1 = max([b[1] for b in panes] + ([ys.max() + 1] if len(ys) else []))
    x0 = min([b[2] for b in panes] + ([xs.min()] if len(xs) else []))
    x1 = max([b[3] for b in panes] + ([xs.max() + 1] if len(xs) else []))
    pad = int(MARGIN * max(shape[0], shape[1]))
    return (max(0, x0 - pad), max(0, y0 - pad),
            min(shape[1], x1 + pad), min(shape[0], y1 + pad))


def vectorize(path):
    name = os.path.splitext(os.path.basename(path))[0]
    rgb = np.asarray(Image.open(path).convert("RGB"))

    panes = detect_panes(rgb)
    pane_mask = np.zeros(rgb.shape[:2], bool)
    for y0, y1, x0, x1 in panes:
        pane_mask[y0:y1, x0:x1] = True

    layers = classify_ink(rgb, pane_mask)
    x0, y0, x1, y1 = content_bbox(layers, panes, rgb.shape)
    w, h = x1 - x0, y1 - y0

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" '
        f'viewBox="{x0} {y0} {w} {h}" width="{w}" height="{h}">',
        f'<rect x="{x0}" y="{y0}" width="{w}" height="{h}" fill="#ffffff"/>',
    ]
    for box in panes:
        parts.append(embed_pane(rgb, box))
    for color, mask in layers.items():
        parts.append(f'<g fill="{PALETTE[color]}" transform="scale(0.5)">')
        for d, tr in trace_layer(mask):
            attr = f' transform="{tr}"' if tr else ""
            parts.append(f'<path d="{d}"{attr}/>')
        parts.append("</g>")
    parts.append("</svg>")

    os.makedirs(OUTPUT, exist_ok=True)
    out = os.path.join(OUTPUT, name + ".svg")
    with open(out, "w") as f:
        f.write("\n".join(parts))
    print(f"{name}: {len(panes)} pane(s), inks {sorted(layers)}, "
          f"{os.path.getsize(out) // 1024} KB")


if __name__ == "__main__":
    files = sys.argv[1:] or sorted(
        os.path.join(FIGURES, f) for f in os.listdir(FIGURES)
        if f.endswith(".png"))
    for f in files:
        vectorize(f)
