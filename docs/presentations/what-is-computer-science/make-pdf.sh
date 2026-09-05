#!/bin/sh
# Regenerate what-is-computer-science.pdf from index.html.
#
# The deck renders itself: index.html?print lays the slides out as a stack of
# 1600x900 pages with every build step shown and every figure drawn once at a
# fixed time, so the output is deterministic. All this script does is drive
# headless Chrome over that page. There is no build step and no dependency —
# the PDF is a rendering of the one file, not a separate artifact to maintain.
#
#   ./make-pdf.sh              light theme, the default for reading and printing
#   THEME=dark ./make-pdf.sh   the deck as it looks on a projector
#   ./make-pdf.sh --check      is the committed PDF current? exit 1 if not
#
# Sync is tracked against the *source*, not the output. Two renders of the same
# index.html do not produce the same bytes — Chrome varies its output run to
# run, and a Linux runner resolves the font stack differently from a Mac — so
# comparing PDFs would report a change every time and commit noise forever.
# Instead each build records the hash of index.html in what-is-computer-science.pdf.sha
# and --check compares that, which answers the only question worth asking:
# was this PDF built from the deck as it stands?

set -eu

cd "$(dirname "$0")"

OUT=what-is-computer-science.pdf
STAMP=$OUT.sha
THEME=${THEME:-light}

sha_of() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | cut -d' ' -f1
  else
    shasum -a 256 "$1" | cut -d' ' -f1
  fi
}

SRC=$(sha_of index.html)

if [ "${1:-}" = "--check" ]; then
  if [ -f "$OUT" ] && [ -f "$STAMP" ] && [ "$(cat "$STAMP")" = "$SRC" ]; then
    echo "make-pdf: $OUT is current"
    exit 0
  fi
  echo "make-pdf: $OUT is stale — run ./make-pdf.sh and commit both it and $STAMP" >&2
  exit 1
fi

CHROME=
for c in \
  "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" \
  "/Applications/Chromium.app/Contents/MacOS/Chromium" \
  "$(command -v google-chrome 2>/dev/null || true)" \
  "$(command -v google-chrome-stable 2>/dev/null || true)" \
  "$(command -v chromium 2>/dev/null || true)" \
  "$(command -v chromium-browser 2>/dev/null || true)"
do
  if [ -n "$c" ] && [ -x "$c" ]; then CHROME=$c; break; fi
done

if [ -z "$CHROME" ]; then
  echo "make-pdf: no Chrome or Chromium found" >&2
  exit 1
fi

PROFILE=$(mktemp -d)
CHROME_PID=
cleanup() {
  [ -n "$CHROME_PID" ] && kill "$CHROME_PID" 2>/dev/null
  rm -rf "$PROFILE"
}
trap cleanup EXIT

rm -f "$OUT"

"$CHROME" \
  --headless=new \
  --disable-gpu \
  --no-sandbox \
  --no-pdf-header-footer \
  --virtual-time-budget=30000 \
  --user-data-dir="$PROFILE" \
  --print-to-pdf="$OUT" \
  "file://$PWD/index.html?print&theme=$THEME" >/dev/null 2>&1 &
CHROME_PID=$!

# Chrome has been known to sit there after writing the file, so wait for the
# PDF to be complete rather than for the process to exit. %%EOF is the marker.
i=0
while [ "$i" -lt 180 ]; do
  if [ -s "$OUT" ] && LC_ALL=C tail -c 64 "$OUT" | grep -aq '%%EOF'; then break; fi
  kill -0 "$CHROME_PID" 2>/dev/null || break
  sleep 1
  i=$((i + 1))
done

kill "$CHROME_PID" 2>/dev/null || true
wait "$CHROME_PID" 2>/dev/null || true
CHROME_PID=

if [ ! -s "$OUT" ] || ! LC_ALL=C tail -c 64 "$OUT" | grep -aq '%%EOF'; then
  echo "make-pdf: Chrome produced no complete PDF" >&2
  exit 1
fi

# page objects, not the /Pages tree nodes: the page tree is nested, so /Count
# is per node and never the total
pages=$(LC_ALL=C grep -ao '/Type */Page[s]*' "$OUT" | grep -vc 'Pages' || true)
slides=$(LC_ALL=C grep -c 'class="slide' index.html || true)
echo "make-pdf: $OUT — $pages pages from $slides slides, $THEME theme"

if [ "$pages" -ne "$slides" ]; then
  echo "make-pdf: page count does not match slide count" >&2
  exit 1
fi

printf '%s\n' "$SRC" > "$STAMP"
