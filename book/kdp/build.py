#!/usr/bin/env python3
"""Build Amazon KDP artifacts from the book draft.

Produces, fully autonomously, in book/kdp/out:

  interior.pdf   print-ready interior (7x10in, embedded fonts, vector figures)
  book.epub      Kindle-ready EPUB3 with vector figures and cover
  cover.png      front cover (1600x2560) for the Kindle edition
  cover.pdf      full print cover wrap (back + spine + front, 0.125in bleed),
                 spine width computed from the actual interior page count

Requires: pandoc, weasyprint, cairosvg, and book/figures-svg (vectorize.py).

Usage: python3 build.py
"""

import html
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
BOOK = os.path.dirname(HERE)
OUT = os.path.join(HERE, "out")
DRAFT = os.path.join(BOOK, "README.md")
FONT_PATH = os.path.join(HERE, "fonts", "Caveat.ttf")

TITLE = "Elementary Computer Science"
SUBTITLE = "From Bits and Bytes to the Universality of Computing"
AUTHOR = "Christoph Kirsch"

# KDP: premium color ink on white paper, 7x10in trim
PAGE_W_IN, PAGE_H_IN = 7.0, 10.0
BLEED_IN = 0.125
SPINE_PER_PAGE_IN = 0.002347  # premium color paper thickness per page


def preprocess(md, target):
    """Adapt the draft markdown for the given target ('print' or 'epub')."""
    # vector figures with text outlined, so no reader needs the font
    md = md.replace("](figures/", "](kdp/out/figures-outlined/")
    md = re.sub(r"\.png( \"|\))", r".svg\1", md)

    # pandoc's gfm reader does not produce <figure> elements, so image
    # paragraphs become raw HTML figures with the alt text as caption
    def figure(m):
        alt, src = html.escape(m.group(1), quote=True), m.group(2)
        return (f'<figure>\n<img src="{src}" alt="{alt}"/>\n'
                f"<figcaption>{m.group(1)}</figcaption>\n</figure>")
    md = re.sub(r'^!\[(.+?)\]\((kdp/out/figures-outlined/[^ )]+)'
                r'(?: "[^"]*")?\)$',
                figure, md, flags=re.M)

    # the remote CC badge cannot (and should not) be fetched at build time
    md = re.sub(r'<a rel="license"[^>]*><img[^>]*/></a><br />', "", md)

    # split title/author/front matter off the top of the draft
    md = re.sub(r"^# .*\n+### by .*\n+", "", md)

    # front-matter headings are unnumbered chapters in print
    md = md.replace("#### Acknowledgements", "## Acknowledgements {.unnumbered}")
    md = md.replace("#### License", "## License {.unnumbered}")

    if target == "print":
        # wrap the hand-written table of contents so CSS can add the
        # printed page number of each entry
        md = md.replace("## Table of Content",
                        '<div id="toc">\n\n## Table of Content {.unnumbered}')
        m = re.search(r'(<div id="toc">.*?)\n(## Introduction)', md, re.S)
        md = md[:m.end(1)] + "\n\n</div>\n\n" + m.group(2) + md[m.end(2):]
    else:
        # the EPUB gets a real navigation TOC from pandoc instead
        md = re.sub(r"## Table of Content.*?(?=## Introduction)", "", md,
                    flags=re.S)

    # glossary is a chapter but not a numbered one
    md = md.replace("## Glossary", "## Glossary {.unnumbered}")
    return md


# ------------------------------------------------------- text outlining

TEXT_RE = re.compile(r'<text x="([\d.-]+)" y="([\d.-]+)" '
                     r'text-anchor="middle" font-family="[^"]*" '
                     r'font-size="([\d.]+)" fill="([^"]*)">(.*?)</text>',
                     re.S)
TSPAN_RE = re.compile(r'<tspan(?:\s+dy="([\d.-]+)")?'
                      r'(?:\s+font-size="([\d.]+)")?>(.*?)</tspan>', re.S)

_GLYPHS = None


def _glyphs():
    global _GLYPHS
    if _GLYPHS is None:
        from fontTools.pens.svgPathPen import SVGPathPen
        from fontTools.ttLib import TTFont
        font = TTFont(FONT_PATH)
        glyphset = font.getGlyphSet()
        cmap = font.getBestCmap()
        upm = font["head"].unitsPerEm
        cache = {}

        def glyph(ch):
            if ch not in cache:
                gname = cmap.get(ord(ch))
                if gname is None:
                    cache[ch] = (None, 0.5 * upm)
                else:
                    pen = SVGPathPen(glyphset)
                    glyphset[gname].draw(pen)
                    cache[ch] = (pen.getCommands(), glyphset[gname].width)
            return cache[ch]
        _GLYPHS = (glyph, upm)
    return _GLYPHS


def outline_text(svg):
    """Replace <text> elements by glyph outline paths (same font), so
    renderers without the Caveat font still show typed labels."""
    glyph, upm = _glyphs()

    def runs_of(body):
        if "<tspan" not in body:
            return [(html.unescape(body), 0.0, None)]
        return [(html.unescape(m.group(3)),
                 float(m.group(1) or 0),
                 float(m.group(2)) if m.group(2) else None)
                for m in TSPAN_RE.finditer(body)]

    def replace(m):
        cx, base, size, fill, body = (float(m.group(1)), float(m.group(2)),
                                      float(m.group(3)), m.group(4),
                                      m.group(5))
        runs = runs_of(body)
        total = sum(sum(glyph(c)[1] for c in run) * (rs or size) / upm
                    for run, _, rs in runs)
        x = cx - total / 2
        y = base
        parts = [f'<g fill="{fill}">']
        for run, dy, rs in runs:
            s = (rs or size) / upm
            y += dy
            for ch in run:
                d, adv = glyph(ch)
                if d:
                    parts.append(
                        f'<path transform="translate({x:.1f} {y:.1f}) '
                        f'scale({s:.4f} {-s:.4f})" d="{d}"/>')
                x += adv * s
        parts.append("</g>")
        return "".join(parts)

    return TEXT_RE.sub(replace, svg)


def outline_figures():
    """figures-svg/*.svg -> out/figures-outlined/*.svg with text as paths."""
    src = os.path.join(BOOK, "figures-svg")
    dst = os.path.join(OUT, "figures-outlined")
    os.makedirs(dst, exist_ok=True)
    for f in sorted(os.listdir(src)):
        if f.endswith(".svg"):
            with open(os.path.join(src, f)) as fh:
                svg = fh.read()
            with open(os.path.join(dst, f), "w") as fh:
                fh.write(outline_text(svg))
    print(f"figures-outlined: {len(os.listdir(dst))} figures")


def pandoc(args, stdin):
    return subprocess.run(
        ["pandoc", "-f", "gfm+attributes+smart", "--wrap=none"] + args,
        input=stdin, capture_output=True, text=True, check=True,
        cwd=BOOK).stdout


def build_interior():
    md = preprocess(open(DRAFT).read(), "print")
    body = pandoc(["-t", "html5", "--highlight-style=monochrome"], md)

    html = f"""<!DOCTYPE html>
<html><head><meta charset="utf-8"><title>{TITLE}</title></head><body>
<header id="title-page">
  <h1>{TITLE}</h1>
  <div class="subtitle">{SUBTITLE}</div>
  <div class="author">Christoph Kirsch</div>
</header>
{body}
</body></html>"""

    from weasyprint import HTML
    doc = HTML(string=html, base_url=BOOK + "/").render(
        stylesheets=[os.path.join(HERE, "interior.css")])
    pdf = os.path.join(OUT, "interior.pdf")
    doc.write_pdf(pdf)
    pages = len(doc.pages)
    print(f"interior.pdf: {pages} pages, "
          f"{os.path.getsize(pdf) // (1 << 20)} MB")
    return pages


def build_epub():
    md = preprocess(open(DRAFT).read(), "epub")
    meta = [
        "--metadata", f"title={TITLE}",
        "--metadata", f"subtitle={SUBTITLE}",
        "--metadata", f"author={AUTHOR}",
        "--metadata", "lang=en-US",
        "--metadata", "rights=CC BY-NC-ND 4.0",
    ]
    epub = os.path.join(OUT, "book.epub")
    pandoc(["-t", "epub3", "--toc", "--toc-depth=2",
            "--split-level=2", "--highlight-style=monochrome",
            f"--css={os.path.join(HERE, 'epub.css')}",
            f"--epub-cover-image={os.path.join(OUT, 'cover.png')}",
            "-o", epub] + meta, md)
    print(f"book.epub: {os.path.getsize(epub) // (1 << 20)} MB")


def figure_art(name, strip_background=True):
    """Inline a vectorized figure's content for use inside cover SVGs."""
    svg = open(os.path.join(BOOK, "figures-svg", name + ".svg")).read()
    vb = re.search(r'viewBox="([\d. ]+)"', svg).group(1).split()
    inner = re.sub(r"^<svg[^>]*>|</svg>$", "", svg.strip())
    if strip_background:
        inner = re.sub(r'<rect[^>]*fill="#ffffff"[^>]*/>', "", inner, count=1)
    return inner, [float(v) for v in vb]


def cover_svg(w_in, h_in, spine_in=None):
    """Cover art: title over the tens-complement number circles."""
    W, H = w_in * 300, h_in * 300  # 300 dpi workspace
    art, vb = figure_art("tens-complement")
    front_x = (w_in - PAGE_W_IN - BLEED_IN) * 300 if spine_in else 0
    # front panel (incl. outer bleed) on a wrap; the whole canvas otherwise
    fw = (PAGE_W_IN + BLEED_IN) * 300 if spine_in else W
    # scale art to ~85% of front panel width, centered on the front panel
    s = 0.85 * fw / vb[2]
    ax = front_x + (fw - vb[2] * s) / 2 - vb[0] * s
    ay = H * 0.52 - vb[3] * s / 2 - vb[1] * s

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" '
        f'viewBox="0 0 {W} {H}">',
        f'<rect width="{W}" height="{H}" fill="#f5f4f0"/>',
        f'<g transform="translate({ax},{ay}) scale({s})">{art}</g>',
    ]
    cx = front_x + fw / 2
    parts.append(
        f'<text x="{cx}" y="{H * 0.14}" text-anchor="middle" '
        f'font-family="EB Garamond" font-size="{fw * 0.075}" '
        f'fill="#141414">{TITLE}</text>')
    sub_size = fw * 0.033
    for i, line in enumerate(("From Bits and Bytes",
                              "to the Universality of Computing")):
        parts.append(
            f'<text x="{cx}" y="{H * 0.19 + i * sub_size * 1.3}" '
            f'text-anchor="middle" font-family="EB Garamond" '
            f'font-style="italic" font-size="{sub_size}" '
            f'fill="#141414">{line}</text>')
    parts.append(
        f'<text x="{cx}" y="{H * 0.93}" text-anchor="middle" '
        f'font-family="EB Garamond" font-size="{fw * 0.04}" '
        f'fill="#141414">{AUTHOR}</text>')

    if spine_in:
        sx = front_x - spine_in * 300 / 2
        parts.append(
            f'<text x="{sx}" y="{H / 2}" text-anchor="middle" '
            f'font-family="EB Garamond" '
            f'font-size="{min(spine_in * 300 * 0.35, 90)}" '
            f'fill="#141414" transform="rotate(90 {sx} {H / 2})">'
            f'{TITLE} · {AUTHOR}</text>')
    parts.append("</svg>")
    return "".join(parts)


def build_covers(pages):
    import cairosvg
    # Kindle front cover, 1600x2560 (Amazon's recommended 1.6:1)
    front = cover_svg(PAGE_H_IN / 1.6, PAGE_H_IN)
    cairosvg.svg2png(bytestring=front.encode(), output_width=1600,
                     write_to=os.path.join(OUT, "cover.png"))
    print("cover.png: 1600x2560 front cover")

    # print wrap: back + spine + front, plus bleed all around
    spine = pages * SPINE_PER_PAGE_IN
    w = 2 * (PAGE_W_IN + BLEED_IN) + spine
    h = PAGE_H_IN + 2 * BLEED_IN
    wrap = cover_svg(w, h, spine_in=spine)
    cairosvg.svg2pdf(bytestring=wrap.encode(),
                     write_to=os.path.join(OUT, "cover.pdf"))
    print(f"cover.pdf: {w:.3f}x{h:.3f} in wrap, "
          f"spine {spine:.3f} in for {pages} pages")


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    outline_figures()
    pages = build_interior()
    build_covers(pages)
    build_epub()
