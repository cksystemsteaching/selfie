# KDP pipeline: from the book draft to the Amazon marketplace

This directory turns the book draft in `book/README.md` and the hand-drawn
figures in `book/figures` into upload-ready Amazon KDP artifacts — fully
autonomously.

## What gets built

Running the two scripts produces:

| artifact | purpose |
| --- | --- |
| `../figures-svg/*.svg` | all 51 figures vectorized and normalized |
| `out/interior.pdf` | print-ready interior, 7 x 10 in, embedded fonts |
| `out/cover.pdf` | print cover wrap (back + spine + front, 0.125 in bleed), spine width computed from the actual page count |
| `out/book.epub` | EPUB3 for the Kindle edition, vector figures, navigation TOC |
| `out/cover.png` | 1600 x 2560 Kindle marketing cover |

## How to run

```bash
# once: pandoc, fonts, and python dependencies
apt-get install pandoc fonts-ebgaramond fonts-jetbrains-mono
pip install numpy scipy pillow vtracer weasyprint cairosvg

python3 vectorize.py   # figures/*.png -> figures-svg/*.svg
python3 build.py       # -> out/interior.pdf, out/cover.*, out/book.epub
```

## How the figures are polished

All figures were drawn in the same app on the same canvas color with a
small set of ink colors, which makes a fully automatic, consistent
treatment possible. `vectorize.py`:

1. **detects embedded code-editor screenshots** (near-white panes) and
   keeps them as high-resolution raster regions inside the SVG — tracing
   antialiased 2-pt editor text would destroy it;
2. **classifies every remaining ink pixel** into a canonical palette so
   ink colors are identical across all figures: amber `#f0a818`, black
   `#141414`, red `#d84808`, orange `#f87008`, green `#30c858`, blue
   `#285098` (each chosen as the modal color of its measured cluster);
3. **traces each ink layer at 2x resolution** with
   [vtracer](https://github.com/visioncortex/vtracer) into smooth spline
   paths — the handwritten stroke shapes are preserved exactly, only the
   representation changes from pixels to geometry;
4. **crops to content** with a uniform 3% margin and normalizes the
   warm-gray canvas to clean white for print.

Typography: EB Garamond (text) and JetBrains Mono (code), both embedded
and subset into the PDF, as KDP requires.

## KDP publishing checklist

The artifacts are designed for these KDP settings:

- **Paperback interior**: 7 x 10 in trim, no bleed, color interior
  (premium color recommended — the figures are the heart of the book).
  Margins are 0.875 in gutter / 0.5 in outside, valid for up to 828 pages.
- **Paperback cover**: upload `out/cover.pdf` as-is. It is regenerated on
  every build because the spine width is `pages x 0.002347 in` (premium
  color paper); rebuild after any change that alters the page count.
  KDP prints a barcode on the lower right of the back cover automatically.
- **Kindle edition**: upload `out/book.epub` plus `out/cover.png`.
  Check the result once with Kindle Previewer; if it complains about
  compressed `.svgz` images, re-run pandoc with `--no-compress` media.
- **Before publishing** you still need to: buy or assign an ISBN (or use
  the free KDP one), add a copyright/edition page (see notes), set
  territories/pricing, and decide how the Creative Commons
  BY-NC-ND license note should read in the published edition.

A 455-page premium-color paperback has a high fixed printing cost;
if a lower-priced edition matters, a grayscale interior variant is easy
to derive from the layered SVGs (map all inks to black) — see NOTES.md.
