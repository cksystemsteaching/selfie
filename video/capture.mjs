// Capture the deck, one PNG per build step, for the explainer video.
//
// The video is not a reimplementation of the talk: it *is* the talk, driven
// through its own build steps by the same API the arrow keys use. That keeps
// the video pixel-identical to what a projector shows and means a change to
// the deck reaches the video by re-running this, with nothing to keep in sync
// by hand.
//
// window.__deck exposes {show, slides}. show(i) on the *current* slide calls
// paint() and returns, so setting slides[i]._step and calling show(i) again
// re-renders that slide at that step -- and the canvas figures follow, since
// the animation loop reads _step every frame.
//
//   node capture.mjs [--only 0,7,10]
//
// Needs Chrome (the same one make-pdf.sh looks for) and puppeteer-core.

import {existsSync, mkdirSync, rmSync} from 'node:fs';
import {dirname, resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import puppeteer from 'puppeteer-core';

const HERE = dirname(fileURLToPath(import.meta.url));
const DECK = resolve(HERE, '../docs/presentations/what-is-selfie/index.html');
const OUT = resolve(HERE, 'remotion/public/slides');

const WIDTH = 1920;
const HEIGHT = 1080;
const THEME = process.env.THEME ?? 'dark';

// The canvas figures grow in over roughly two seconds of their own clock, so
// the first still of a slide waits for them to settle. Later steps only wait
// for the fragment transition (.38s) plus a frame or two.
const SETTLE_FIRST = 2600;
const SETTLE_STEP = 700;

// The slides of the ~10 minute cut, as indices into the 29-slide deck. Keep
// this in step with SLIDES in make-video.py -- the ids are the shared key.
// `last` caps the build at a step below the slide's own maximum, for build
// steps that speak to a live audience and mean nothing on video.
export const CUT = [
  {id: 'slide01', deck: 0, last: 3}, // step 4 is the keyboard legend
  {id: 'slide02', deck: 1},
  {id: 'slide03', deck: 7},
  {id: 'slide04', deck: 9},
  {id: 'slide05', deck: 10},
  {id: 'slide06', deck: 12},
  {id: 'slide07', deck: 13},
  {id: 'slide08', deck: 16},
  {id: 'slide09', deck: 17},
  {id: 'slide10', deck: 18},
  {id: 'slide11', deck: 19},
  {id: 'slide12', deck: 23},
  {id: 'slide13', deck: 27},
  {id: 'slide14', deck: 28},
];

const CHROME = [
  '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
  '/Applications/Chromium.app/Contents/MacOS/Chromium',
  '/usr/bin/google-chrome',
  '/usr/bin/chromium',
].find((p) => existsSync(p));

if (!CHROME) {
  console.error('capture: no Chrome or Chromium found');
  process.exit(1);
}

const onlyArg = process.argv.indexOf('--only');
const only =
  onlyArg > -1 ? new Set(process.argv[onlyArg + 1].split(',').map(Number)) : null;

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

const browser = await puppeteer.launch({
  executablePath: CHROME,
  headless: 'new',
  args: [`--window-size=${WIDTH},${HEIGHT}`, '--hide-scrollbars', '--force-device-scale-factor=1'],
});

const page = await browser.newPage();
await page.setViewport({width: WIDTH, height: HEIGHT, deviceScaleFactor: 1});
await page.goto(`file://${DECK}?theme=${THEME}`, {waitUntil: 'load'});
await page.waitForFunction('window.__deck && window.__deck.slides.length');

// Chrome that a viewer does not need: the nav buttons, the speaker clock, and
// the progress bar and page number, both of which count 29 slides and would
// contradict a 14-slide cut.
await page.addStyleTag({
  content: `.nav,#bar,#pageno{display:none!important}#clock{visibility:hidden!important}`,
});

if (!only) {
  rmSync(OUT, {recursive: true, force: true});
}
mkdirSync(OUT, {recursive: true});

const index = [];
for (const {id, deck, last} of CUT) {
  if (only && !only.has(deck)) {
    continue;
  }
  let maxStep = await page.evaluate((i) => {
    window.__deck.show(i);
    return window.__deck.slides[i]._max;
  }, deck);
  if (last !== undefined) {
    maxStep = Math.min(maxStep, last);
  }
  await sleep(SETTLE_FIRST);

  for (let step = 0; step <= maxStep; step++) {
    await page.evaluate(
      (i, s) => {
        const d = window.__deck;
        d.slides[i]._step = s;
        d.show(i); // same slide -> paint() at the new step
      },
      deck,
      step
    );
    await sleep(step === 0 ? 200 : SETTLE_STEP);
    const file = `${OUT}/${id}-s${String(step).padStart(2, '0')}.png`;
    await page.screenshot({path: file, type: 'png'});
  }
  index.push({id, deck, steps: maxStep + 1});
  console.log(`  ${id}  deck slide ${deck + 1}  ${maxStep + 1} stills`);
}

await browser.close();
console.log(`captured ${index.reduce((n, s) => n + s.steps, 0)} stills into ${OUT}`);
