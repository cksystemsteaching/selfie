#!/bin/sh
# Render one class deck to a PDF next to it.
#
#   docs/classes/make-pdf.sh ics/02-size            light theme, for reading
#   THEME=dark docs/classes/make-pdf.sh ics/02-size the projector version
#   docs/classes/make-pdf.sh ics/02-size --check    is the committed PDF current?
#
# The deck renders itself: index.html?print lays the slides out as a stack of
# 1600x900 pages with every build step shown and every figure inlined, and
# this script drives headless Chrome over that page. A class deck is not one
# file the way the talks are — it loads the shared engine in deck/ and its
# figures from docs/figures/ — so the sync stamp hashes all of them: the
# deck, deck.css, deck.js, and every figure the deck names. Chrome does not
# render deterministically, so the PDF bytes themselves are never compared.

set -eu

HERE=$(cd "$(dirname "$0")" && pwd)
DECK=${1:?usage: make-pdf.sh <class>/<deck> [--check]}
DIR=$HERE/$DECK
[ -f "$DIR/index.html" ] || { echo "make-pdf: no $DIR/index.html" >&2; exit 1; }
cd "$DIR"

NAME=$(basename "$DECK")
OUT=$NAME.pdf
STAMP=$OUT.sha
THEME=${THEME:-light}

sha_of() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum | cut -d' ' -f1
  else shasum -a 256 | cut -d' ' -f1; fi
}

# everything the rendering depends on, in a fixed order
sources() {
  cat index.html "$HERE/deck/deck.css" "$HERE/deck/deck.js"
  grep -o 'data-fig="[^"]*"' index.html | cut -d'"' -f2 | sort -u | while read -r f; do
    [ -f "$HERE/../figures/$f.svg" ] && cat "$HERE/../figures/$f.svg"
  done
}
SRC=$(sources | sha_of)

if [ "${2:-}" = "--check" ]; then
  if [ -f "$OUT" ] && [ -f "$STAMP" ] && [ "$(cat "$STAMP")" = "$SRC" ]; then
    echo "make-pdf: $DECK/$OUT is current"; exit 0
  fi
  echo "make-pdf: $DECK/$OUT is stale — run docs/classes/make-pdf.sh $DECK and commit both it and $STAMP" >&2
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
[ -n "$CHROME" ] || { echo "make-pdf: no Chrome or Chromium found" >&2; exit 1; }

PROFILE=$(mktemp -d)
CHROME_PID=
cleanup() { [ -n "$CHROME_PID" ] && kill "$CHROME_PID" 2>/dev/null; rm -rf "$PROFILE"; }
trap cleanup EXIT

rm -f "$OUT"

# --allow-file-access-from-files lets the deck fetch its figures over file://
"$CHROME" \
  --headless=new \
  --disable-gpu \
  --no-sandbox \
  --allow-file-access-from-files \
  --no-pdf-header-footer \
  --virtual-time-budget=30000 \
  --user-data-dir="$PROFILE" \
  --print-to-pdf="$OUT" \
  "file://$DIR/index.html?print&theme=$THEME" >/dev/null 2>&1 &
CHROME_PID=$!

i=0
while [ "$i" -lt 180 ]; do
  if [ -s "$OUT" ] && LC_ALL=C tail -c 64 "$OUT" | grep -aq '%%EOF'; then break; fi
  kill -0 "$CHROME_PID" 2>/dev/null || break
  sleep 1; i=$((i + 1))
done
kill "$CHROME_PID" 2>/dev/null || true
wait "$CHROME_PID" 2>/dev/null || true
CHROME_PID=

if [ ! -s "$OUT" ] || ! LC_ALL=C tail -c 64 "$OUT" | grep -aq '%%EOF'; then
  echo "make-pdf: Chrome produced no complete PDF" >&2; exit 1
fi

pages=$(LC_ALL=C grep -ao '/Type */Page[s]*' "$OUT" | grep -vc 'Pages' || true)
slides=$(LC_ALL=C grep -c 'class="slide' index.html || true)
echo "make-pdf: $DECK/$OUT — $pages pages from $slides slides, $THEME theme"
if [ "$pages" -ne "$slides" ]; then
  echo "make-pdf: page count does not match slide count" >&2; exit 1
fi
printf '%s\n' "$SRC" > "$STAMP"
