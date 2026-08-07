# Notes from the automated book-production pass

Observations made while building the KDP edition — local improvement
potential in the draft and the figures, beyond what the pipeline already
does automatically.

## Text fixes applied to the draft

One spelling pass was applied directly to `book/README.md` (~35 fixes),
all unambiguous misspellings, e.g. `compilter` → `compiler`,
`Morever` → `Moreover`, `appearence` → `appearance`, `Havard` → `Harvard`
(architecture), `halfs` → `halves`, `casted` → `cast`,
`errorprone` → `error-prone`, `or rath result` → `or rather result`.

## Text: worth an author's look

- **"senidenary"** ("The etymologically correct term for hexadecimal is
  *senidenary*"): the form found in the literature is usually *sedenary*
  (from Latin *sedecim*). Worth double-checking before print.
- **Links in print**: the draft's ~23 external links (mostly in the
  Recommended Readings sections) render as plain text in the print
  interior — the URLs are invisible on paper. Consider a CSS rule that
  prints `href` after the link text in those sections, or spelling out
  URLs that matter.
- **Copyright page**: the print edition still needs a proper
  copyright/edition page (ISBN, edition, year, license). The build
  currently generates only a title page; a copyright page block can be
  added to `build.py` once the ISBN exists.
- **Front matter order**: Acknowledgements currently precede the License
  and TOC. Conventional order would be title, copyright/license, TOC,
  acknowledgements.
- Occasional idioms could be tightened in a deeper editing pass
  (e.g. "hinted on" → "hinted at", "in the meantime" density); the
  automated pass deliberately only fixed unambiguous misspellings.

## Figures: worth an author's look

- **Embedded code screenshots stay raster.** 17 figures (the `scanning-*`,
  `emitting-*`, `atoi`, `scanner`, `parsing-literals`,
  `global-variable-declaration`, `variable-use`, `integer-literal-FSM`
  family) contain code-editor screenshots. The pipeline keeps them as
  embedded high-resolution raster panes, which prints fine at 300 dpi, but
  the panes could eventually be regenerated as real (vector) text from
  `selfie.c` line ranges — each pane's line numbers are visible in the
  screenshots, so this is mechanizable per figure.
- **The densest hybrid figures** (`emitting-literals`,
  `emitting-assignments`, `emitting-expressions`) carry three columns of
  content and reach the legibility limit at 7 x 10 in portrait. Candidates
  for splitting into two figures or rotating to landscape on their page.
- **Ink-role consistency**: colors are now identical across figures, but
  the *role* of a color still varies (labels are black in the FSM figures
  and amber elsewhere; red is sometimes emphasis, sometimes the signed
  interpretation). A tasteful follow-up would be a per-figure color-role
  legend or a one-time harmonization of roles.
- **`vonNeumann.png` vs `machine.png`** overlap heavily (both draw the
  von Neumann architecture); the book text references both, which is fine,
  but they could share one drawing style/level of detail.
- The **CC license badge** in the draft is fetched from creativecommons.org
  at render time on GitHub; the build strips it (the license sentence
  stays). A local vector badge would also fix offline rendering on GitHub.

## Pipeline caveats

- The EPUB stores figures as compressed `.svgz` (pandoc default). Kindle
  Previewer accepts current uploads, but if a device chokes, re-pack with
  uncompressed SVG.
- `epubcheck` is not installed in this environment; the EPUB is
  pandoc-generated (structurally reliable) but has not been formally
  validated here.
- Spine text needs ~0.0625 in clearance on both sides; at 455 pages the
  1.07 in spine has ample room. Below ~100 pages KDP disallows spine text;
  `build.py` does not yet guard for that.
