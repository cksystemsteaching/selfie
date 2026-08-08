#!/usr/bin/env python3
"""Redraw the hand-drawn book figures with crisp geometry.

Builds on vectorize.py (palette classification, screenshot panes, vtracer
tracing) but instead of tracing every stroke, each ink layer is split into
geometry and handwriting:

  1. the layer's skeleton is turned into a stroke graph (endpoints,
     junctions, point chains),
  2. components with long or structural strokes are treated as geometry,
     small wiggly components (letters, digits, formulas) stay handwriting,
  3. geometry strokes are refit: near-straight runs become exact lines,
     near-horizontal/vertical lines snap to shared axis coordinates (so
     grids align and corners square up), long curved runs (curly braces,
     curved arrows, FSM transitions) become smooth cubic beziers,
  4. hand-drawn arrowheads (V-shaped barb strokes or hooked tips) are
     replaced by uniform triangular heads aligned with the shaft,
  5. solid blobs (state dots, wire junctions) become true circles,
  6. handwriting is traced with vtracer exactly as before.

Usage: python3 beautify.py [figure.png ...]   (default: all figures)
Output: book/figures-svg/<name>.svg
"""

import math
import os
import sys

import numpy as np
import sknw
from PIL import Image
from scipy import ndimage
from skimage.morphology import skeletonize

from vectorize import (CANVAS, FIGURES, OUTPUT, PALETTE, classify_ink,
                       content_bbox, detect_panes, embed_pane, trace_layer)

# An edge is geometry when it is at least this long (fraction of the
# figure diagonal), or straight and at least the shorter length.
GEOM_LEN = 0.040
GEOM_STRAIGHT_LEN = 0.020

SNAP_DEG = 7.0          # snap lines within this angle of horizontal/vertical
CURVE_TOL = 2.2         # bezier fit tolerance, in units of stroke width
BARB_LEN = 0.030        # arrowhead barbs are at most this * diagonal long
DOT_SOLIDITY = 0.62     # filled fraction of bbox above which a blob is a dot


def diag(shape):
    return math.hypot(shape[0], shape[1])


# ---------------------------------------------------------------- stroke graph

def stroke_graph(mask):
    """sknw graph of the mask's skeleton plus stroke width and skeleton."""
    skel = skeletonize(mask)
    dist = ndimage.distance_transform_edt(mask)
    width = 2.0 * np.median(dist[skel]) if skel.any() else 3.0
    graph = sknw.build_sknw(skel.astype(np.uint8), multi=True)
    return graph, width, skel


def edge_points(graph, u, v, key):
    """Point chain of an edge as float (x, y) array, endpoints included."""
    pts = graph[u][v][key]["pts"].astype(float)
    pu, pv = graph.nodes[u]["o"], graph.nodes[v]["o"]
    if len(pts) == 0 or np.hypot(*(pts[0] - pu)) > np.hypot(*(pts[-1] - pu)):
        pts = pts[::-1]
    chain = np.vstack([pu, pts, pv])
    return chain[:, ::-1]  # row/col -> x/y


def rdp(points, eps):
    """Ramer-Douglas-Peucker indices of a polyline's corner vertices."""
    keep = [0, len(points) - 1]
    stack = [(0, len(points) - 1)]
    while stack:
        a, b = stack.pop()
        if b - a < 2:
            continue
        seg = points[b] - points[a]
        n = np.hypot(*seg)
        rel = points[a + 1:b] - points[a]
        if n == 0:
            d = np.hypot(*rel.T)
        else:
            d = np.abs(seg[0] * rel[:, 1] - seg[1] * rel[:, 0]) / n
        i = int(np.argmax(d))
        if d[i] > eps:
            keep.append(a + 1 + i)
            stack.extend([(a, a + 1 + i), (a + 1 + i, b)])
    return sorted(set(keep))


# ---------------------------------------------------------------- bezier fit

def fit_bezier(points, tol):
    """Schneider-style piecewise cubic fit through a point run."""
    if len(points) < 3:
        return [["L", points[-1]]]
    t0 = points[1] - points[0]
    t1 = points[-2] - points[-1]
    return _fit(points, _unit(t0), _unit(t1), tol)


def _unit(v):
    n = np.hypot(*v)
    return v / n if n > 0 else v


def _fit(pts, tan0, tan1, tol, depth=0):
    if len(pts) == 2:
        d = np.hypot(*(pts[1] - pts[0])) / 3.0
        return [["C", pts[0] + tan0 * d, pts[1] + tan1 * d, pts[1]]]
    u = np.r_[0, np.cumsum(np.hypot(*np.diff(pts, axis=0).T))]
    u /= u[-1]
    bez = _lsq_bezier(pts, u, tan0, tan1)
    err, split = _max_error(pts, bez, u)
    if err < tol or depth >= 12:
        return [["C", bez[1], bez[2], bez[3]]]
    tc = _unit(pts[min(split + 1, len(pts) - 1)] - pts[split - 1])
    return (_fit(pts[:split + 1], tan0, tc, tol, depth + 1) +
            _fit(pts[split:], -tc if False else tc, tan1, tol, depth + 1))


def _lsq_bezier(pts, u, tan0, tan1):
    b0 = (1 - u) ** 3
    b1 = 3 * u * (1 - u) ** 2
    b2 = 3 * u ** 2 * (1 - u)
    b3 = u ** 3
    a0 = tan0[None, :] * b1[:, None]
    a1 = tan1[None, :] * b2[:, None]
    rhs = (pts - pts[0][None, :] * (b0 + b1)[:, None]
           - pts[-1][None, :] * (b2 + b3)[:, None])
    c00 = (a0 * a0).sum()
    c01 = (a0 * a1).sum()
    c11 = (a1 * a1).sum()
    x0 = (a0 * rhs).sum()
    x1 = (a1 * rhs).sum()
    det = c00 * c11 - c01 * c01
    if abs(det) > 1e-9:
        l0 = (x0 * c11 - x1 * c01) / det
        l1 = (c00 * x1 - c01 * x0) / det
    else:
        l0 = l1 = 0.0
    d = np.hypot(*(pts[-1] - pts[0])) / 3.0
    if l0 <= 0 or l1 <= 0:
        l0 = l1 = d
    return [pts[0], pts[0] + tan0 * l0, pts[-1] + tan1 * l1, pts[-1]]


def _max_error(pts, bez, u):
    b0 = (1 - u) ** 3
    b1 = 3 * u * (1 - u) ** 2
    b2 = 3 * u ** 2 * (1 - u)
    b3 = u ** 3
    curve = (bez[0][None, :] * b0[:, None] + bez[1][None, :] * b1[:, None] +
             bez[2][None, :] * b2[:, None] + bez[3][None, :] * b3[:, None])
    d = np.hypot(*(curve - pts).T)
    i = int(np.argmax(d))
    return d[i], max(1, min(i, len(pts) - 2))


# ---------------------------------------------------------------- classify

def component_masks(mask):
    labels, n = ndimage.label(mask, structure=np.ones((3, 3)))
    return labels, n


def is_dot(comp, d):
    """Large solid round blob: an FSM state dot. Small marks (periods,
    quotes) stay handwriting — at dot size the difference is invisible."""
    ys, xs = np.nonzero(comp)
    h, w = np.ptp(ys) + 1, np.ptp(xs) + 1
    if max(h, w) > 1.6 * min(h, w):
        return None
    filled = ndimage.binary_fill_holes(comp)
    if comp.sum() < 0.88 * filled.sum():  # rings and letters are not solid
        return None
    if comp.sum() < DOT_SOLIDITY * h * w:
        return None
    r = math.sqrt(comp.sum() / math.pi)
    if r < 0.006 * d:
        return None
    return (xs.mean(), ys.mean(), r)


def ekey(u, v, k):
    return (min(u, v), max(u, v), k)


# ---------------------------------------------------------------- geometry

class Geometry:
    """Refits one component's stroke graph into crisp segments and curves.

    Edges are classified individually: long (or long-and-straight) edges
    are geometry; short bridges between geometry edges (wire hops, tiny
    connectors) join them; everything else — letters and digits drawn
    touching a line — stays handwriting. Barb edges consumed by arrowheads
    and overshoot spurs at junctions are dropped entirely.
    """

    def __init__(self, graph, width, shape):
        self.g = graph
        self.w = width
        self.d = diag(shape)
        self.node_pos = {n: np.array(graph.nodes[n]["o"][::-1], float)
                         for n in graph.nodes}
        self.heads = []      # (tip, direction) triangles to emit
        self.consumed = set()  # edges replaced by arrowheads
        self.dropped = set()   # spurs omitted from the drawing
        self.marked = set()    # geometry edges
        self.mark()

    def mark(self):
        lengths = {}
        for u, v, k in self.g.edges(keys=True):
            pts = edge_points(self.g, u, v, k)
            length = np.hypot(*np.diff(pts, axis=0).T).sum()
            lengths[ekey(u, v, k)] = length
            # extent, not length: a letter loop is long but compact
            extent = math.hypot(np.ptp(pts[:, 0]), np.ptp(pts[:, 1]))
            chord = pts[-1] - pts[0]
            ang = math.degrees(math.atan2(chord[1], chord[0])) % 90
            near_axis = min(ang, 90 - ang) <= 15
            if extent >= GEOM_LEN * self.d or (
                    near_axis and length >= GEOM_STRAIGHT_LEN * self.d and
                    _is_straight(pts, 0.6 * self.w)):
                self.marked.add(ekey(u, v, k))
        # an isolated straightish stroke of letter size is handwriting
        # (ascenders of l, d, k qualify as straight): geometry must be
        # long or connect to other geometry
        while True:
            lone = [e for e in self.marked
                    if lengths[e] < 0.05 * self.d and not self._touches(e)]
            if not lone:
                break
            self.marked.difference_update(lone)
        if not self.marked:
            return
        # short bridges whose both ends touch geometry join it; short
        # terminal scraps at geometry junctions are tracing overshoot
        for u, v, k in self.g.edges(keys=True):
            e = ekey(u, v, k)
            if e in self.marked:
                continue
            touches = [any(ekey(a, b, kk) in self.marked
                           for a, b, kk in self.g.edges(n, keys=True)
                           if ekey(a, b, kk) != e) for n in (u, v)]
            terminal = self.g.degree(u) == 1 or self.g.degree(v) == 1
            if all(touches) and lengths[e] < 1.8 * self.w:
                self.dropped.add(e)
            elif all(touches) and lengths[e] <= 8.0 * self.w:
                # a short connector between geometry edges: rounded corner,
                # wire hop — but not a letter loop leaning on a line
                self.marked.add(e)
            elif any(touches) and terminal and lengths[e] < 3.0 * self.w:
                self.dropped.add(e)

    def _touches(self, e):
        for n in e[:2]:
            for a, b, kk in self.g.edges(n, keys=True):
                if ekey(a, b, kk) != e and ekey(a, b, kk) in self.marked:
                    return True
        return False

    def edges(self):
        return [(u, v, k) for u, v, k in self.g.edges(keys=True)
                if ekey(u, v, k) in self.marked
                and ekey(u, v, k) not in self.consumed]

    def detect_arrowheads(self):
        """Replace V-shaped barb edges at the tip of long edges by markers."""
        barb_max = BARB_LEN * self.d
        for u, v, k in self.edges():
            pts = edge_points(self.g, u, v, k)
            length = np.hypot(*np.diff(pts, axis=0).T).sum()
            if length < 2.5 * barb_max:
                continue
            for node, end in ((u, 0), (v, -1)):
                barbs = []
                fars = []
                for uu, vv, kk in self.g.edges(node, keys=True):
                    if ekey(uu, vv, kk) == ekey(u, v, k) or \
                            ekey(uu, vv, kk) in self.marked:
                        continue  # geometry is never an arrowhead barb
                    far = vv if uu == node else uu
                    # a barb dead-ends, or its tip rests on geometry
                    # (arrows drawn touching the box they point at)
                    if far == node or (self.g.degree(far) != 1 and not any(
                            ekey(a, b, c) in self.marked
                            for a, b, c in self.g.edges(far, keys=True))):
                        continue
                    if far in fars:  # two edges rejoining: a letter loop
                        continue
                    bpts = edge_points(self.g, uu, vv, kk)
                    blen = np.hypot(*np.diff(bpts, axis=0).T).sum()
                    if 1.5 * self.w <= blen <= barb_max:
                        barbs.append((uu, vv, kk))
                        fars.append(far)
                if not barbs:
                    continue
                tip = pts[end]
                ref = pts[max(2, len(pts) // 6)] if end == 0 else \
                    pts[-max(3, len(pts) // 6) - 1]
                dirv = _unit(tip - ref)
                if self.continues(node, (u, v, k), dirv):
                    continue  # the shaft carries on: not an arrow tip
                straight = _is_straight(pts, self.w)
                sides = set()
                good = []
                single = None
                for uu, vv, kk in barbs:
                    far = self.node_pos[vv if uu == node else uu]
                    back = _unit(far - tip)
                    # a real barb points backward, off to one side
                    if np.dot(back, dirv) < -0.25:
                        sides.add(back[0] * dirv[1] - back[1] * dirv[0] > 0)
                        good.append((uu, vv, kk))
                    if np.dot(back, dirv) < -0.4:
                        single = (uu, vv, kk)
                if len(good) >= 2 and len(sides) == 2:
                    hit = good
                elif single is not None and straight:
                    # a single hooked barb at the tip of a straight shaft
                    hit = [single]
                else:
                    continue
                for uu, vv, kk in hit:
                    self.consumed.add(ekey(uu, vv, kk))
                self.heads.append((tip, dirv))

    def continues(self, node, shaft, dirv):
        """True when a marked edge leaves the node along the shaft
        direction — the stroke passes through rather than ending here."""
        for uu, vv, kk in self.g.edges(node, keys=True):
            if ekey(uu, vv, kk) == ekey(*shaft) or \
                    ekey(uu, vv, kk) not in self.marked:
                continue
            pts = edge_points(self.g, uu, vv, kk)
            if np.hypot(*(pts[0] - self.node_pos[node])) > \
                    np.hypot(*(pts[-1] - self.node_pos[node])):
                pts = pts[::-1]
            out = _unit(pts[min(len(pts) - 1, 8)] - pts[0])
            if np.dot(out, dirv) > 0.7:
                return True
        return False

    def strip_hook(self, pts, free=(True, True)):
        """Drop a short sharply-turned tail (hand-drawn hooked arrow tip).
        Hooks only exist at free ends — a sharp wiggle where a stroke
        meets a junction is just pen noise, not an arrow tip."""
        idx = rdp(pts, max(2.5, self.w))
        if len(idx) < 3:
            return pts, None
        for end in (len(idx) - 1, 0):
            if not free[1 if end else 0]:
                continue
            i2, i1 = (idx[-2], idx[-1]) if end else (idx[1], idx[0])
            tail = np.hypot(*(pts[i1] - pts[i2]))
            if not (self.w * 1.5 < tail < BARB_LEN * self.d):
                continue
            j = idx[-3] if end else idx[2]
            a = _unit(pts[i2] - pts[j])
            b = _unit(pts[i1] - pts[i2])
            if np.dot(a, b) < 0.15:  # sharp turn: it's a hook, not the shaft
                keep = pts[:i2 + 1] if end else pts[i2:]
                length = np.hypot(*np.diff(keep, axis=0).T).sum()
                # only straight shafts carry hooked arrow tips; curly ends
                # of braces and loops are part of the drawing
                if length > 2.5 * tail and _is_straight(keep, self.w):
                    return keep, (pts[i2], a if end else -a)
        return pts, None

    def refit(self):
        """Classify each edge's runs into straight lines and bezier curves."""
        self.detect_arrowheads()
        segments, curves = [], []
        for u, v, k in self.edges():
            pts = edge_points(self.g, u, v, k)
            length = np.hypot(*np.diff(pts, axis=0).T).sum()
            terminal = self.g.degree(u) == 1 or self.g.degree(v) == 1
            # drop noise and terminal overshoot spurs at junctions
            if length < (3.0 * self.w if terminal else 1.2 * self.w):
                self.dropped.add(ekey(u, v, k))
                continue
            pts, hook = self.strip_hook(
                pts, (self.g.degree(u) == 1, self.g.degree(v) == 1))
            if hook is not None:
                self.heads.append(hook)
            eps = max(2.5, self.w * 0.9)
            idx = rdp(pts, eps)
            chord = np.hypot(*(pts[-1] - pts[0]))
            if _is_straight(pts, 1.3 * self.w):
                segments.append([pts[0].copy(), pts[-1].copy(), (u, v)])
            elif len(idx) <= 2 or (len(idx) <= 4 and chord > 0.9 * length):
                for a, b in zip(idx, idx[1:]):
                    segments.append([pts[a].copy(), pts[b].copy(), (u, v)])
            else:
                curves.append([pts, (u, v)])
        return segments, curves

    def snap(self, segments):
        """Snap near-axis segments to exact H/V and cluster coordinates."""
        hs, vs = [], []
        for seg in segments:
            p, q, _ = seg
            dx, dy = q - p
            ang = math.degrees(math.atan2(dy, dx)) % 180
            if min(ang, 180 - ang) < SNAP_DEG:
                hs.append(seg)
            elif abs(ang - 90) < SNAP_DEG:
                vs.append(seg)
        for group, axis in ((hs, 1), (vs, 0)):
            vals = [(s[0][axis] + s[1][axis]) / 2 for s in group]
            for s, val in zip(group, vals):
                snapped = _cluster_snap(val, vals, self.w * 1.6)
                s[0][axis] = s[1][axis] = snapped
        segments = self.merge_retraces(segments, hs, vs)
        self.weld(segments, hs, vs)
        return segments

    def merge_retraces(self, segments, hs, vs):
        """Collapse overlapping near-parallel segments (pen retraces at
        box corners and along lines) into the longer one."""
        gone = set()
        for i, a in enumerate(segments):
            for b in segments[i + 1:]:
                if id(a) in gone or id(b) in gone:
                    continue
                da, la = _unit(a[1] - a[0]), np.hypot(*(a[1] - a[0]))
                db, lb = _unit(b[1] - b[0]), np.hypot(*(b[1] - b[0]))
                if abs(np.dot(da, db)) < 0.966:  # ~15 degrees
                    continue
                keep, drop = (a, b) if la >= lb else (b, a)
                d, l = (da, la) if la >= lb else (db, lb)
                rel0, rel1 = drop[0] - keep[0], drop[1] - keep[0]
                off = max(abs(d[0] * rel0[1] - d[1] * rel0[0]),
                          abs(d[0] * rel1[1] - d[1] * rel1[0]))
                if off > 2.5 * self.w:
                    continue
                t = sorted((np.dot(rel0, d), np.dot(rel1, d)))
                overlap = min(t[1], l) - max(t[0], 0)
                if overlap < 0.5 * min(l, np.hypot(*(drop[1] - drop[0]))):
                    continue
                lo, hi = min(t[0], 0), max(t[1], l)
                p0 = keep[0].copy()
                keep[0][:] = p0 + d * lo
                keep[1][:] = p0 + d * hi
                gone.add(id(drop))
        return [s for s in segments if id(s) not in gone]

    def weld(self, segments, hs, vs):
        """Extend segment endpoints to meet nearby snapped axis lines,
        closing corners and T-joints that snapping pulled apart."""
        tol = 3.0 * self.w
        for seg in segments:
            p, q, _ = seg
            d = _unit(q - p)
            for pt in (p, q):
                for group, axis in ((hs, 1), (vs, 0)):
                    for t in group:
                        if t is seg:
                            continue
                        line = t[0][axis]
                        lo = min(t[0][1 - axis], t[1][1 - axis]) - 2 * self.w
                        hi = max(t[0][1 - axis], t[1][1 - axis]) + 2 * self.w
                        if abs(pt[axis] - line) <= tol and abs(d[axis]) > 0.1:
                            hit = pt[1 - axis] + (line - pt[axis]) * \
                                d[1 - axis] / d[axis]
                            if lo <= hit <= hi:
                                pt[axis] = line
                                pt[1 - axis] = hit
                                break


def _cluster_snap(val, vals, tol):
    near = [v for v in vals if abs(v - val) <= tol]
    return sum(near) / len(near)


def _is_straight(pts, w):
    """True when a run never strays more than ~a stroke width off its chord."""
    chord = pts[-1] - pts[0]
    length = np.hypot(*np.diff(pts, axis=0).T).sum()
    n = np.hypot(*chord)
    if n == 0 or n < 0.85 * length:
        return False
    rel = pts - pts[0]
    dev = np.abs(chord[0] * rel[:, 1] - chord[1] * rel[:, 0]) / n
    return dev.max() < 2.2 * w


# ---------------------------------------------------------------- svg emit

def svg_path_curves(pts, tol):
    parts = [f"M{pts[0][0]:.1f} {pts[0][1]:.1f}"]
    for cmd in fit_bezier(pts, tol):
        if cmd[0] == "L":
            parts.append(f"L{cmd[1][0]:.1f} {cmd[1][1]:.1f}")
        else:
            c1, c2, p = cmd[1], cmd[2], cmd[3]
            parts.append(f"C{c1[0]:.1f} {c1[1]:.1f} {c2[0]:.1f} {c2[1]:.1f} "
                         f"{p[0]:.1f} {p[1]:.1f}")
    return "".join(parts)


def arrowhead(tip, dirv, width):
    l = max(4.2 * width, 14.0)
    w2 = 0.42 * l
    b = tip - dirv * l
    n = np.array([-dirv[1], dirv[0]])
    p1, p2 = b + n * w2, b - n * w2
    return (f'<path d="M{tip[0]:.1f} {tip[1]:.1f} L{p1[0]:.1f} {p1[1]:.1f} '
            f'L{p2[0]:.1f} {p2[1]:.1f} Z"/>')


def hand_pixels(comp, graph, geo, hand_edges, w):
    """Component pixels that belong to handwriting edges.

    Handwriting keeps its full glyph: every pixel within a stroke radius
    of a handwriting skeleton — overlap with redrawn geometry is harmless
    since both are painted the same color. Hand edges that hug the
    geometry (pen retraces along a line) duplicate it and are dropped.
    """
    geoskel = np.zeros_like(comp)
    for u, v, k in graph.edges(keys=True):
        e = ekey(u, v, k)
        if e in geo.marked or e in geo.consumed:
            pts = graph[u][v][k]["pts"]
            geoskel[pts[:, 0], pts[:, 1]] = True
    gd = ndimage.distance_transform_edt(~geoskel) if geoskel.any() else None
    handskel = np.zeros_like(comp)
    for u, v, k in hand_edges:
        pts = graph[u][v][k]["pts"]
        if gd is not None and len(pts) and gd[pts[:, 0], pts[:, 1]].max() \
                < 1.6 * w:
            continue  # retrace hugging a redrawn line
        handskel[pts[:, 0], pts[:, 1]] = True
    hand_nodes = set()
    for u, v, k in hand_edges:
        hand_nodes.update((u, v))
    geo_nodes = set()
    for u, v, k in graph.edges(keys=True):
        if ekey(u, v, k) not in hand_edges:
            geo_nodes.update((u, v))
    for n in hand_nodes - geo_nodes:
        pts = graph.nodes[n]["pts"]
        handskel[pts[:, 0], pts[:, 1]] = True
    if not handskel.any():
        return np.zeros_like(comp)
    hd = ndimage.distance_transform_edt(~handskel)
    return comp & (hd <= 0.8 * w)


def floating_heads(hand, all_segs, heads, barb_max, width):
    """Arrowheads drawn as V strokes detached from their shaft (often
    leaning on the box they point at) become crisp heads; the shaft is
    extended to the V's apex. Matched V pixels are erased from the
    handwriting mask."""
    labels, n = ndimage.label(hand, structure=np.ones((3, 3)))
    for sl, i in zip(ndimage.find_objects(labels), range(1, n + 1)):
        comp = labels[sl] == i
        ys, xs = np.nonzero(comp)
        if math.hypot(np.ptp(ys), np.ptp(xs)) > 1.2 * barb_max:
            continue
        if ndimage.binary_fill_holes(comp).sum() > 1.15 * comp.sum():
            continue  # rings (letter o, digit 0) are not arrowheads
        pix = np.column_stack(
            [xs + sl[1].start, ys + sl[0].start]).astype(float)
        best = None
        for seg in all_segs:
            for tip, tail in ((seg[1], seg[0]), (seg[0], seg[1])):
                dirv = _unit(tip - tail)
                d = np.hypot(*(pix - tip).T).min()
                if d > 1.5 * width:
                    continue
                proj = (pix - tip) @ dirv
                perp = (pix - tip) @ np.array([-dirv[1], dirv[0]])
                # the V sits just ahead of the tip and converges forward
                if proj.min() < -2.5 * width or proj.max() > 1.3 * barb_max:
                    continue
                prange = proj.max() - proj.min()
                if prange < max(2.5 * width, 0.5 * np.ptp(perp)):
                    continue  # a bar across the tip, not a V along it
                if abs(perp.mean()) > 0.22 * np.ptp(perp):
                    continue  # a head straddles its shaft symmetrically
                at_apex = proj > proj.max() - 0.25 * prange
                if np.ptp(perp[at_apex]) > 3.0 * width:
                    continue  # does not converge to a point
                at_back = proj < proj.max() - 0.6 * prange
                if not at_back.any() or perp[at_back].max() < 1.0 * width \
                        or perp[at_back].min() > -1.0 * width:
                    continue  # arms must spread both ways behind the apex
                if best is None or d < best[0]:
                    apex = tip + dirv * proj.max()
                    best = (d, seg, tip is seg[1], apex, dirv)
        if best is not None:
            _, seg, at_end, apex, dirv = best
            seg[1 if at_end else 0][:] = apex
            heads.append((apex, dirv))
            hand[sl][comp] = False


def weld_curves(all_curves, all_segs, w):
    """Snap curve endpoints onto nearby geometry so outlines close:
    first to segment endpoints, then onto segment spans, then to other
    curve endpoints."""
    tol = 2.5 * w
    ends = [(pts, i) for pts, _ in all_curves for i in (0, -1)]
    seg_pts = [s[i] for s in all_segs for i in (0, 1)]
    for pts, i in ends:
        p = pts[i]
        best = None
        for q in seg_pts:
            d = np.hypot(*(q - p))
            if d <= tol and (best is None or d < best[0]):
                best = (d, q)
        if best is None:
            for s in all_segs:
                a, b = s[0], s[1]
                ab = b - a
                l2 = ab @ ab
                if l2 == 0:
                    continue
                t = np.clip((p - a) @ ab / l2, 0.0, 1.0)
                q = a + t * ab
                d = np.hypot(*(q - p))
                if d <= tol and (best is None or d < best[0]):
                    best = (d, q)
        if best is not None:
            pts[i] = best[1]
            continue
        for opts, oi in ends:
            if opts is pts:
                continue
            d = np.hypot(*(opts[oi] - p))
            if d <= tol and (best is None or d < best[0]):
                best = (d, opts[oi])
        if best is not None:
            mid = (p + best[1]) / 2
            pts[i] = mid
            for opts, oi in ends:
                if opts is not pts and np.hypot(*(opts[oi] - best[1])) < 1e-6:
                    opts[oi] = mid


def beautify_layer(mask, color, shape):
    """Split a layer into geometry (crisp) and handwriting (traced)."""
    labels, n = component_masks(mask)
    hand = np.zeros_like(mask)
    out = []
    dots = []
    width = max(2.2, stroke_width(mask))
    all_segs, all_curves, heads = [], [], []
    slices = ndimage.find_objects(labels)
    for i in range(1, n + 1):
        sl = slices[i - 1]
        pad = 2
        y0, y1 = max(0, sl[0].start - pad), min(mask.shape[0], sl[0].stop + pad)
        x0, x1 = max(0, sl[1].start - pad), min(mask.shape[1], sl[1].stop + pad)
        comp = labels[y0:y1, x0:x1] == i
        dot = is_dot(comp, diag(shape))
        if dot is not None:
            cx, cy, r = dot
            dots.append((cx + x0, cy + y0, r))
            continue
        graph, w, skel = stroke_graph(comp)
        geo = Geometry(graph, w, shape) if graph.number_of_edges() else None
        if geo is None or not geo.marked:
            hand[y0:y1, x0:x1] |= comp
            continue
        segments, curves = geo.refit()
        segments = geo.snap(segments)
        off = np.array([x0, y0], float)
        for seg in segments:
            seg[0] += off
            seg[1] += off
            all_segs.append(seg)
        for pts, _ in curves:
            all_curves.append((pts + off, w))
        for tip, dirv in geo.heads:
            heads.append((tip + off, dirv))
        hand_edges = {ekey(u, v, k) for u, v, k in graph.edges(keys=True)
                      if ekey(u, v, k) not in geo.marked
                      and ekey(u, v, k) not in geo.consumed
                      and ekey(u, v, k) not in geo.dropped}
        if hand_edges:
            hand[y0:y1, x0:x1] |= hand_pixels(comp, graph, geo, hand_edges, w)

    if all_segs:
        floating_heads(hand, all_segs, heads, BARB_LEN * diag(shape), width)
    if all_curves:
        weld_curves(all_curves, all_segs, width)

    stroke = []
    for p, q, _ in all_segs:
        stroke.append(f'<path d="M{p[0]:.1f} {p[1]:.1f} '
                      f'L{q[0]:.1f} {q[1]:.1f}"/>')
    for pts, w in all_curves:
        stroke.append(f'<path d="{svg_path_curves(pts, CURVE_TOL * w)}"/>')
    if stroke:
        out.insert(0, f'<g fill="none" stroke="{PALETTE[color]}" '
                      f'stroke-width="{width:.1f}" stroke-linecap="round" '
                      f'stroke-linejoin="round">' + "".join(stroke) + "</g>")
    for tip, dirv in heads:
        out.append(arrowhead(tip, dirv, width))
    for cx, cy, r in dots:
        out.append(f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="{r:.1f}"/>')
    return out, hand


def stroke_width(mask):
    if not mask.any():
        return 3.0
    skel = skeletonize(mask)
    dist = ndimage.distance_transform_edt(mask)
    return 2.0 * float(np.median(dist[skel])) if skel.any() else 3.0


# ---------------------------------------------------------------- driver

def beautify(path):
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
        geo_parts, hand = beautify_layer(mask, color, rgb.shape)
        parts.append(f'<g fill="{PALETTE[color]}">')
        parts.extend(geo_parts)
        if hand.any():
            parts.append('<g transform="scale(0.5)">')
            for d, tr in trace_layer(hand):
                attr = f' transform="{tr}"' if tr else ""
                parts.append(f'<path d="{d}"{attr}/>')
            parts.append("</g>")
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
        beautify(f)
