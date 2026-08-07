# The selfie explainer video

A ~13 minute narrated cut of [What is Selfie?](../docs/presentations/what-is-selfie/),
the 29-slide talk, for people who will watch a video but will not open a deck.
Fourteen of the twenty-nine slides, narrated end to end: the length is set by what
the argument needs rather than by a target, which is why the operating-systems
stretch runs a third of the video.

**Watch:** <https://youtu.be/aWT2jLb1MVA> — or `selfie-explainer.mp4` once you have
built it, which is not committed (see *What is and is not in git*).
**Description and chapters:** [description.txt](description.txt), as uploaded.

The video is **not** a reimplementation of the talk. `capture.mjs` drives the deck
itself through its own build steps in headless Chrome and writes one still per step,
so every frame is exactly what a projector shows. Narration is written one string per
build step, so the deck builds itself in time with the voice rather than sitting still
under it. Change the deck, re-run the capture, and the video follows.

## The pipeline

```bash
cd video
npm install                                   # puppeteer-core, for the capture
python3 -m venv .venv && ./.venv/bin/pip install chatterbox-tts 'setuptools<81' soundfile

node capture.mjs                              # 71 stills from the 14 slides of the cut
./.venv/bin/python make-video.py --voice-clone voice-ref-cc06-4321.wav
```

`make-video.py` synthesizes one wav per slide, writes `remotion/src/narration.json`
(per-slide durations and the timestamp of every build step), runs `remotion render`,
and regenerates `description.txt` with chapter marks derived from the audio.

`--audio-only` and `--render-only` split those halves. `--only slide03,slide07`
re-synthesizes just those slides and re-measures the rest from their wavs, so an
interrupted run resumes correctly. This is a 16 GB machine and Chatterbox on MPS
climbs until it swaps, so prefer one slide per process:

```bash
for s in $(seq -w 1 14); do
  ./.venv/bin/python make-video.py --audio-only \
    --voice-clone voice-ref-cc06-4321.wav --only slide$s
done
```

A partial manifest is a normal intermediate state — it records `"complete": false`
and `render()` refuses to run on one, rather than quietly producing a short video.

## The voice

The narration is the author's voice, cloned zero-shot by
[Chatterbox](https://github.com/resemble-ai/chatterbox) from twelve seconds of his
own Compiler Construction lectures. The lecture recordings are not in this
repository, and neither is the reference clip. To rebuild it:

```bash
afconvert "CC06 Target Machine, part 1.mp4" cc06.wav -f WAVE -d LEI16@24000 -c 1
# cut 12 s from 43:21.5, normalize to 0.85 peak
```

Two details that matter more than the choice of lecture:

- **`CLONE_CFG_WEIGHT = 0.3`.** At Chatterbox's default guidance of 0.5 the clone
  drifts toward a neutral American accent no matter which clip it is given. 0.3
  follows the reference's prosody closely enough to keep the author's German accent,
  at the cost of a slightly slower delivery — which nothing has to absorb by hand,
  because every timing in the manifest is measured from the audio.
- **The clip must open on speech.** Chatterbox conditions on roughly the first 6 s
  (speaker encoder) and 10 s (decoder), so a leading pause is spent conditioning
  budget and a longer clip buys nothing. 43:21.5 is not a guess: it is the densest
  twelve seconds of speech within twenty seconds either side that also starts on a
  word. The recording clips almost everywhere — the 99th percentile of its envelope
  is 1.0 — which is why the recipe normalizes down rather than hunting for an
  unclipped window.

Sampling seeds are pinned per build step, so a re-run reproduces the same narration.
Chatterbox watermarks its output (Perth).

This follows `scripts/explainer_video.py` in the hurdy-gurdy repository, which is
where the recipe came from; the difference here is that narration is chunked by build
step rather than by sentence, so the manifest can drive the animation.

## The cut

Fourteen of the deck's twenty-nine slides. The three selves, the operating-systems
argument in full, the tools, and the invitation:

| video | deck | |
|---|---|---|
| 01 | 1 | One file |
| 02 | 2 | Three commands |
| 03 | 8 | The system |
| 04 | 10 | What a compiler really is |
| 05 | 11 | Self-compilation |
| 06 | 13 | Self-execution |
| 07 | 14 | Self-hosting |
| 08 | 17 | Two ways to build one operating system |
| 09 | 18 | They are the same operating system |
| 10 | 19 | So why virtualize? |
| 11 | 20 | The price is self-reference |
| 12 | 24 | What you can decide about a program |
| 13 | 28 | Why learn this now |
| 14 | 29 | Take a selfie |

The mapping lives twice, in `CUT` in `capture.mjs` and `SLIDES` in `make-video.py`,
keyed by slide id. `make-video.py` refuses to run if a slide's still count and its
narration step count disagree, which is what catches the two drifting apart.

Dropped, and where they went: the deck's part titles carry no argument on video;
trusting trust (deck 12) and Rice (deck 23) are folded into the narration of video 12;
the C\* and RISC-U slides (deck 6 and 7) into video 03. The video is rendered from
the **dark** theme — it is the projector version, and it is what looks right in a
player.

## What is and is not in git

Committed: `capture.mjs`, `make-video.py`, the Remotion project, `description.txt`,
this file. Everything needed to rebuild.

Ignored: the `.venv`, `node_modules`, the voice reference, the synthesized audio, the
captured stills, and the MP4 itself. The whole point of this repository is that it is
twelve thousand lines in one file; a few hundred megabytes of derived video does not
belong in it. Publish the MP4 wherever videos go and leave the recipe here.
