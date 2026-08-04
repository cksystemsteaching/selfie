#!/usr/bin/env python3
"""Generate the selfie explainer video (YouTube-ready MP4).

A ~10 minute cut of the 29-slide talk at docs/presentations/what-is-selfie.
The video is not a reimplementation of that deck: capture.mjs drives the deck
itself through its own build steps in headless Chrome and writes one still per
step, so the video shows exactly what a projector shows, and a change to the
deck reaches the video by re-running the capture.

Narration is written one string per build step. Each step is synthesized
separately, so the manifest knows when every step begins and Remotion can
advance the build in time with the voice -- the deck animates itself to the
narration rather than sitting still under it.

Two narration engines, as in hurdy-gurdy's scripts/explainer_video.py, which
this is modelled on:
  - default: Kokoro (hexgrad/Kokoro-82M, voice af_heart)
  - --voice-clone REF.wav: Chatterbox (ResembleAI) zero-shot cloning from a
    clean speech sample; sampling seeds are pinned per step so the output is
    reproducible, and Chatterbox watermarks the audio (Perth).

The shipped cut clones the author's voice from his Compiler Construction
lectures, which are not in the repository. To rebuild the reference:

    afconvert "CC06 Target Machine, part 1.mp4" cc06.wav -f WAVE -d LEI16@24000 -c 1
    # then cut 12 s from 43:21.5 and normalize to 0.85 peak (the source clips
    # nearly everywhere -- the 99th percentile of its envelope is 1.0)

That window is not arbitrary: it is the densest twelve seconds of speech
within twenty seconds either side that also *opens* on speech, which matters
because Chatterbox conditions on roughly the first 6 s (speaker encoder) and
10 s (decoder), so a leading pause is spent conditioning budget.

Usage:
  python3 make-video.py [--audio-only | --render-only]
                        [--voice-clone REF.wav]
                        [--only slideNN,slideNN,...]

--only re-synthesizes just the named slides, keeping the others' wavs (which
must already exist); their timings are re-measured from those wavs, so an
interrupted run resumes correctly.

On this 16 GB machine, prefer one slide per process --

    for s in $(seq -w 1 14); do
      python3 make-video.py --audio-only --voice-clone voice-ref-cc06-4321.wav --only slide$s
    done

-- which reclaims everything between slides.
"""

import json
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REMOTION = HERE / "remotion"
AUDIO_DIR = REMOTION / "public" / "audio"
SLIDE_DIR = REMOTION / "public" / "slides"
MANIFEST = REMOTION / "src" / "narration.json"
OUT_MP4 = HERE / "selfie-explainer.mp4"

FPS = 30
LEAD_IN = 0.5    # silence before narration starts on each slide
TAIL = 1.2       # silence after narration ends before the next slide
VOICE = "af_heart"
SAMPLE_RATE = 24000
STEP_GAP = 0.28  # silence between build steps: the beat a speaker leaves

# Chatterbox classifier-free guidance. The default 0.5 sands the author's
# German accent off the clone; 0.3 keeps it by following the reference's
# prosody more closely, at the cost of a slightly slower delivery (which the
# manifest absorbs -- every timing here is derived from the audio).
CLONE_CFG_WEIGHT = 0.3

REPO_URL = "github.com/cksystemsteaching/selfie"
TALK_URL = "selfie.cs.uni-salzburg.at/talk"

# --------------------------------------------------------------------------
# Narration. One entry per slide of the cut; one string per build step of that
# slide, in order, so step k is on screen while string k is spoken.
#
# Written for TTS: names are respelled phonetically (C* -> "C star", RISC-U ->
# "risk you", selfie1.m -> "selfie one dot m", BTOR2 -> "beetor two") so the
# synthesized speech says what the slide shows. The chapter titles become
# YouTube chapters in description.txt.
# --------------------------------------------------------------------------

SLIDES: list[tuple[str, str, list[str]]] = [
    ("slide01", "One file", [
        "This is selfie.",
        "One file. Twelve thousand three hundred and ninety four lines of C. "
        "It compiles itself, it executes itself, and it hosts itself.",
        "Inside that file there are four things. Star C, a compiler that "
        "compiles its own source. Mipster, an emulator that executes its own "
        "machine code. Hypster, a hypervisor whose virtual machines can run "
        "the hypervisor. And the little library all three of them run on.",
        "There are no dependencies, no framework, and no build system. "
        "Nothing is hidden below it. You can read all of it, and in one "
        "semester my students do.",
    ]),
    ("slide02", "Three commands", [
        "Here is the whole talk in three commands. Each one is a different "
        "kind of self-reference, and each one you can run tonight.",
        "The first: selfie compiles its own source to machine code. Then it "
        "runs that machine code, and has it compile the same source again. "
        "The two results are identical. Byte for byte.",
        "The second: selfie compiles its own emulator, and then the emulator "
        "executes itself.",
        "And the third: the hypervisor creates a virtual machine, and inside "
        "that virtual machine, it runs the hypervisor.",
        "Understand the first and you understand compilers. The second, "
        "machines. The third, operating systems. That is the deal.",
    ]),
    ("slide03", "The system", [
        "So what is in the file? A path that runs all the way down, with "
        "nothing in the middle left out.",
        "A scanner turns characters into symbols, a parser turns symbols into "
        "code. There is no syntax tree in between: selfie generates machine "
        "code while it parses, in one pass, which is much of why it fits.",
        "Then registers, the stack, procedure calls, a symbol table, and a "
        "linker that works in memory. And a disassembler, to read back what "
        "it just wrote.",
        "Underneath, a runtime: a garbage collector conservative enough to "
        "collect its own data structures, caches, a profiler, and a debugger "
        "that replays the instructions before a crash. The language has seven "
        "keywords. The machine has fourteen instructions.",
    ]),
    ("slide04", "What a compiler really is", [
        "Now the idea underneath all three selves. It sounds like philosophy. "
        "It is the most practical thing here.",
        "What does a while loop mean? Not what the manual says. It means "
        "whatever the compiler emits, a comparison and a branch, and whatever "
        "the machine then does with those.",
        "So the meaning of a program is fixed by another program. And that "
        "other program is written in the same language.",
        "This is an English dictionary written in English. It is a paradox "
        "only if you insist the definitions come first. They do not. The "
        "machine comes first, and the dictionary is bootstrapped onto it.",
        "Keep two colours for the rest of this. Ochre is syntax: notation, "
        "the thing you can check. Cyan is semantics: what actually happens, "
        "the thing you cannot.",
    ]),
    ("slide05", "Self-compilation", [
        "The first self. The compiler compiles its own source, and gets the "
        "same answer twice.",
        "Start by borrowing a meaning. An ordinary C compiler builds "
        "selfie dot c once. C star is a subset of C, so this works, and it is "
        "the only outside help the system ever gets.",
        "Now use it on itself. That binary compiles selfie dot c to machine "
        "code. Call it selfie one dot m. Its meaning still came from the "
        "foreign compiler.",
        "So close the loop. Run selfie one dot m, and have it compile "
        "selfie dot c again. Call that selfie two dot m: a compiler compiled "
        "by itself.",
        "The two are identical, byte for byte. That equality is a fixed "
        "point, and it is where the system stops depending on anything "
        "outside itself. It is also the hardest test in the project: change "
        "the code generator, and your compiler has to be good enough to "
        "generate the compiler that contains it.",
    ]),
    ("slide06", "Self-execution", [
        "The second self, and a different loop for a different reason.",
        "Mipster is an interpreter for the machine, written in C star. Fetch "
        "a word, decode it, do what it says, move the program counter.",
        "Compile mipster with star C and you get machine code for an "
        "interpreter of machine code. Load that into mipster, and mipster is "
        "executing mipster.",
        "And the inner one cannot tell. Code cannot ask whether the processor "
        "underneath it is silicon or software. Unless it can see a clock, "
        "which is the one thing that gives an emulator away.",
        "What it costs is time. One instruction up there is a few thousand "
        "down here. Printing a usage line takes eighty six thousand "
        "instructions on the bare machine, and two hundred and twenty two "
        "million when a mipster emulates the mipster that runs it.",
    ]),
    ("slide07", "Self-hosting", [
        "The third self, and this one is genuinely hard to build.",
        "Hypster does not interpret anything. It creates virtual machines and "
        "asks the machine below it to run them, by context switching. Save "
        "these registers, load those, go.",
        "Its virtual machines are good enough to host all of selfie: the "
        "compiler, the emulator, and hypster itself. Stack as many as you "
        "like, in any order.",
        "That is what self-hosting means, and selfie does it recursively, "
        "which most production hypervisors do not.",
        "One rule: every tower stands on a mipster. Context switching has to "
        "come from somewhere, and stock hardware does not offer it in the "
        "form hypster needs, so the bottom of the stack is always an emulated "
        "machine.",
    ]),
    ("slide08", "Two ways to build one operating system", [
        "Which brings us to the part I would keep if I only had five minutes. "
        "There are two ways to build the same operating system, and the "
        "difference between them is why operating systems have a reputation "
        "for being impossible to understand.",
        "By emulation, the operating system contains an interpreter. Guest "
        "instructions are read and carried out by the operating system's own "
        "code. The guest never touches the processor. Isolation is free, "
        "because the guest is only ever data being read, and data cannot "
        "escape.",
        "By virtualization, the operating system sets up a page table and a "
        "timer, then lets the guest run on the real processor, taking control "
        "back on faults, calls and interrupts. Now isolation has to be "
        "constructed, because the guest and the kernel share the same "
        "hardware.",
    ]),
    ("slide09", "They are the same operating system", [
        "And here is the claim. An operating system built by emulation is "
        "semantically equivalent to one built by virtualization.",
        "Not similar. Equivalent, down to every bit the guest can observe. "
        "There is no experiment the guest can run that tells them apart, "
        "except by looking at a clock.",
        "And this is not something I am asking you to believe. It is "
        "something you can measure, on a laptop, in about a minute.",
        "Host selfie on an operating system built each way. Under emulation "
        "the guest executes eighty six thousand three hundred and eighty "
        "instructions. Under virtualization: eighty six thousand three "
        "hundred and eighty. The same number, because it is the same "
        "computation.",
        "Selfie even ships a procedure called mixter, which switches a "
        "running machine between the two mechanisms mid-execution. Nothing "
        "notices, because from the guest's point of view nothing happened.",
        "Which has a consequence worth stopping on. If the two are "
        "equivalent, and one is dramatically simpler, then the simple one "
        "defines what the complicated one must do. Build the emulated version "
        "first and you have a running answer key for the virtualized one.",
        "That is not a classroom trick. It is how parts of real operating "
        "systems get verified: an interpreter as the reference, and the fast "
        "implementation checked against it.",
    ]),
    ("slide10", "So why virtualize?", [
        "So if the two are equivalent, why does every operating system on "
        "earth choose the hard one? For exactly one reason. Performance.",
        "Same guest, same output, the same eighty six thousand instructions "
        "of actual work. What differs is the bill sent to the machine "
        "underneath.",
        "Bare metal, eighty six thousand. Virtualized, about two hundred "
        "times more. With another monitor underneath, seven hundred times. "
        "Emulated, two and a half thousand times, because interpretation "
        "costs a few thousand instructions per instruction.",
        "So virtualization wins by a factor of twelve here, and by far more "
        "on real work, because the cost of a context switch is fixed and gets "
        "amortised. Give the guest something substantial to do, like "
        "compiling itself, and the overhead falls from two hundred times to "
        "one point seven. Production systems get close to one. That is why "
        "the cloud exists.",
    ]),
    ("slide11", "The price is self-reference", [
        "And now the price. Virtualization is emulation, plus self-reference.",
        "The kernel runs on the same processor as its guests. To be isolated "
        "from them, it must itself run in a virtual machine. And who manages "
        "that one?",
        "That is the bootstrapping problem, and it is where the difficulty of "
        "operating systems actually lives. Real systems answer it with kernel "
        "code that never uses the abstractions it provides. It must not "
        "fault, because it is the thing that handles faults.",
        "Shrink that to the minimum and what is left is a microkernel: the "
        "trusted base everything else stands on. Small enough that people "
        "have proved it correct.",
        "So, the whole part in one line. Emulation is isolation. "
        "Virtualization is isolation plus self-reference. Take the "
        "self-reference out, teach everything else against the simple design, "
        "then put it back on purpose, and you can see the hard thing on its "
        "own instead of tangled up with paging and scheduling. That is what "
        "nobody told me when I was a student.",
    ]),
    ("slide12", "What you can decide about a program", [
        "There is a second half to selfie: what a machine can decide about a "
        "program. Rice's theorem, from nineteen fifty three, says every "
        "non-trivial question about a program's behaviour is undecidable. "
        "Questions about its text are safe; questions about its meaning are "
        "not. So every useful tool is a deliberate approximation, and selfie "
        "ships several to compare.",
        "Monster does symbolic execution, turning machine code into a formula "
        "satisfiable exactly when some input makes the program fail.",
        "Beator does the same as bounded model checking, and adds memory "
        "access outside the blocks you allocated.",
        "Rotor takes the full instruction set rather than the teaching "
        "subset, and generates models that let you synthesize code rather "
        "than only check it.",
        "Bitme is a concurrent model checker over those models, driving "
        "solvers and binary decision diagrams.",
        "Beatle draws the formulae as graphs, so you can look at what your "
        "program means.",
        "And there is a Rust implementation with a browser visualiser.",
        "Every one is self-applicable: each translates code including all of "
        "selfie, and including itself. You can hand a symbolic execution "
        "engine its own machine code and ask a solver about it.",
        "And then you hit the wall, which is the fun part. Deciding whether "
        "those formulae are satisfiable is N P complete. You can watch syntax "
        "become semantics and run into the limits of computation before the "
        "coffee gets cold.",
    ]),
    ("slide13", "Why learn this now", [
        "Which leaves the question everyone is holding. Why learn this when a "
        "machine will write the code for you?",
        "Because generation got cheap and verification did not. Producing "
        "plausible code is nearly free. Deciding whether it is right is as "
        "hard as it was in nineteen fifty three, and Rice's theorem does not "
        "care who wrote the program. Value moves to the two ends: saying "
        "precisely what should be true, and establishing that it is.",
        "Because the stack did not disappear. Every model that writes your "
        "code runs on virtualized machines, compiled by a compiler, scheduled "
        "by a kernel. When it is slow, or wrong, or leaking, the person who "
        "can go down there is the person who fixes it.",
        "And because depth is not downloadable. Knowing where a field is "
        "thin, and where it is about to give, comes from having lived inside "
        "a subject. Selfie is small enough to live inside all of it.",
        "The frontier is not proving things inside a language. Machines are "
        "formidable at that. It is finding the truth you cannot yet prove, "
        "and building the language that captures it.",
        "Which is the argument of a companion lecture, if you want the long "
        "version.",
    ]),
    ("slide14", "Take a selfie", [
        "So. Fifteen minutes from now you could be running a compiler that "
        "compiles itself.",
        "Clone it, type make, and run the third command. No C compiler? There "
        "is a docker image. No terminal at all? It runs in a browser tab. "
        "Then open the source, find the last line before the exit code, and "
        "print your own name. That is assignment one, and it is genuinely how "
        "the course starts.",
        "There is a book that builds all of this from bits and bytes, "
        "classroom slides, and an autograder that grades your work before you "
        "submit it. All public, all in the repository.",
        "The full talk this is cut from is at selfie dot c s dot uni "
        "salzburg dot a t, slash talk. The code is on GitHub. Come and take a "
        "selfie.",
    ]),
]


def configure_espeak() -> None:
    """Point phonemizer at a working espeak-ng install (Kokoro path only)."""
    import misaki.espeak  # noqa: F401
    from phonemizer.backend.espeak.wrapper import EspeakWrapper

    candidates = [
        (os.environ.get("ESPEAK_NG_LIBRARY"), os.environ.get("ESPEAK_NG_DATA")),
        ("/opt/homebrew/lib/libespeak-ng.dylib", "/opt/homebrew/share/espeak-ng-data"),
        ("/usr/local/lib/libespeak-ng.dylib", "/usr/local/share/espeak-ng-data"),
        ("/usr/lib/x86_64-linux-gnu/libespeak-ng.so.1", "/usr/lib/x86_64-linux-gnu/espeak-ng-data"),
    ]
    for lib, data in candidates:
        if lib and data and Path(lib).exists() and (Path(data) / "phontab").exists():
            EspeakWrapper.set_library(lib)
            EspeakWrapper.set_data_path(data)
            return
    sys.exit("no usable espeak-ng found; try `brew install espeak-ng`")


def _kokoro_speaker():
    configure_espeak()
    from kokoro import KPipeline

    pipeline = KPipeline(lang_code="a", repo_id="hexgrad/Kokoro-82M")

    def speak(text: str, seed: int):
        import numpy as np

        return np.concatenate([a.numpy() for _, _, a in pipeline(text, voice=VOICE)])

    return speak


def _chatterbox_speaker(ref_path: str):
    import torch

    # MPS is much faster but its buffers are wired, and one generation can hold
    # several gigabytes on a 16 GB machine -- enough that the system swaps and
    # sampling collapses to seconds per step. SELFIE_TTS_DEVICE=cpu trades
    # speed for a run that finishes.
    device = os.environ.get("SELFIE_TTS_DEVICE") or (
        "mps" if torch.backends.mps.is_available() else "cpu")
    if device == "mps":  # checkpoints are saved for cuda; retarget the load
        _load = torch.load
        torch.load = lambda *a, **k: _load(
            *a, **{**k, "map_location": k.get("map_location", torch.device("mps"))}
        )
    from chatterbox.tts import ChatterboxTTS

    model = ChatterboxTTS.from_pretrained(device=device)
    if model.sr != SAMPLE_RATE:
        sys.exit(f"chatterbox sample rate {model.sr} != {SAMPLE_RATE}")

    def speak(text: str, seed: int):
        import numpy as np

        # One step of narration is one or two sentences, which is well inside
        # what Chatterbox handles in a single generation, so the build step is
        # the chunk and no further splitting is needed.
        torch.manual_seed(seed)
        wav = model.generate(text, audio_prompt_path=ref_path,
                             cfg_weight=CLONE_CFG_WEIGHT)
        out = wav.squeeze(0).cpu().numpy()
        # MPS shares system RAM and its allocator caches what it frees, so a
        # long run climbs until the machine swaps -- at which point sampling
        # falls off a cliff. Hand the buffers back after every step.
        if device == "mps":
            torch.mps.empty_cache()
        return np.asarray(out, dtype="float32")

    return speak


def step_images(slide_id: str, n_steps: int) -> list[str]:
    """The stills capture.mjs wrote for this slide, one per build step."""
    imgs = sorted(p.name for p in SLIDE_DIR.glob(f"{slide_id}-s*.png"))
    if len(imgs) != n_steps:
        sys.exit(f"{slide_id}: {len(imgs)} stills but {n_steps} narration steps "
                 f"-- re-run `node capture.mjs`, or fix SLIDES")
    return imgs


def synthesize(clone_ref: str | None, only: set[str] | None = None) -> list[dict]:
    """Render one wav per slide; return the manifest entries."""
    import numpy as np
    import soundfile as sf

    prior = {}
    if MANIFEST.exists():
        prior = {s["id"]: s for s in json.loads(MANIFEST.read_text())["slides"]}

    speak = _chatterbox_speaker(clone_ref) if clone_ref else _kokoro_speaker()
    voice_label = (f"cloned:{Path(clone_ref).name}@cfg{CLONE_CFG_WEIGHT}"
                   if clone_ref else VOICE)
    AUDIO_DIR.mkdir(parents=True, exist_ok=True)
    gap = np.zeros(int(STEP_GAP * SAMPLE_RATE), dtype="float32")

    entries = []
    seed = 0
    for slide_id, chapter, steps in SLIDES:
        imgs = step_images(slide_id, len(steps))
        if only is not None and slide_id not in only:
            # Re-measure the kept wav rather than trusting the manifest: a run
            # interrupted partway leaves new wavs on disk and a manifest still
            # describing the old ones, and believing it would drift every
            # later slide out of sync with its own narration.
            wav, kept = AUDIO_DIR / f"{slide_id}.wav", prior.get(slide_id)
            seed += len(steps)
            if not (wav.exists() and kept):
                # Not done yet. Synthesis is long and this machine is small,
                # so a partial manifest is a normal intermediate state rather
                # than an error; render() is what refuses to run on one.
                print(f"  {slide_id}  {'--':>5}   {chapter}  (not yet)")
                continue
            kept["seconds"] = sf.info(wav).frames / SAMPLE_RATE
            entries.append(kept)
            print(f"  {slide_id}  {kept['seconds']:5.1f}s  {chapter}  (kept)")
            continue

        parts, marks, t = [], [], 0.0
        for i, text in enumerate(steps):
            audio = speak(text, seed=seed + i)
            if i:
                parts.append(gap)
                t += STEP_GAP
            marks.append({"image": f"slides/{imgs[i]}", "at": round(t, 3)})
            parts.append(audio)
            t += len(audio) / SAMPLE_RATE
            print(f"    step {i}  {len(audio)/SAMPLE_RATE:5.1f}s")
        seed += len(steps)

        audio = np.concatenate(parts)
        peak = float(np.abs(audio).max())
        if peak > 0.9:
            audio *= 0.9 / peak
        sf.write(AUDIO_DIR / f"{slide_id}.wav", audio, SAMPLE_RATE)
        dur = len(audio) / SAMPLE_RATE
        entries.append({"id": slide_id, "seconds": round(dur, 3), "steps": marks})
        print(f"  {slide_id}  {dur:5.1f}s  {chapter}")

    MANIFEST.write_text(json.dumps({
        "fps": FPS,
        "leadInSeconds": LEAD_IN,
        "tailSeconds": TAIL,
        "voice": voice_label,
        "complete": len(entries) == len(SLIDES),
        "slides": entries,
    }, indent=2) + "\n")
    if len(entries) != len(SLIDES):
        print(f"\n  manifest is partial: {len(entries)}/{len(SLIDES)} slides done")
    return entries


def render() -> None:
    if not json.loads(MANIFEST.read_text()).get("complete"):
        sys.exit("manifest is partial -- synthesize the remaining slides first")
    if not (REMOTION / "node_modules").exists():
        subprocess.run(["npm", "install", "--no-audit", "--no-fund"],
                       cwd=REMOTION, check=True)
    concurrency = os.environ.get("REMOTION_CONCURRENCY", "2")
    subprocess.run(
        ["npx", "remotion", "render", "Explainer", str(OUT_MP4),
         f"--concurrency={concurrency}"],
        cwd=REMOTION, check=True,
    )


def write_description(entries: list[dict]) -> None:
    chapters, t = [], 0.0
    for (_, chapter, _), e in zip(SLIDES, entries):
        m, s = divmod(int(t), 60)
        chapters.append(f"{m:02d}:{s:02d} {chapter}")
        t += LEAD_IN + e["seconds"] + TAIL
    # Read the runtime off the audio rather than writing a number that drifts
    # the first time a line of narration changes.
    minutes = round(t / 60)

    (HERE / "description.txt").write_text(f"""selfie in {minutes} minutes: a system that compiles, executes and hosts itself

Selfie is a self-contained 12KLOC C implementation of a self-compiling
compiler, a self-executing emulator, and a self-hosting hypervisor -- an
educational platform for teaching the design and implementation of compilers,
libraries, operating systems and virtual machine monitors, built around the
one thing those subjects have in common and textbooks tend to step over:
self-reference in systems code.

This is a cut of the full talk. It walks the three selves -- compiling,
executing and hosting yourself -- and then spends its middle on the
distinction that makes operating systems hard to understand: an operating
system built by emulation is semantically equivalent to one built by
virtualization. The same guest executes the same 86,380 instructions either
way. Virtualization is needed only for performance -- and it buys that
performance by introducing self-reference, which is the bootstrapping problem,
the trusted computing base, and the whole microkernel programme.

Every number quoted is measured, and the commands that produce them are in the
repository.

The full 29-slide talk, in your browser: https://{TALK_URL}
Code, book, slides and autograder: https://{REPO_URL}

Narrated with a voice cloned from the author's Compiler Construction lectures.

{chr(10).join(chapters)}
""")


def main() -> None:
    args = sys.argv[1:]
    clone_ref = None
    if "--voice-clone" in args:
        i = args.index("--voice-clone")
        if i + 1 >= len(args):
            sys.exit(__doc__)
        clone_ref = args[i + 1]
        del args[i:i + 2]
        if not Path(clone_ref).exists():
            sys.exit(f"no such reference audio: {clone_ref}")

    only = None
    if "--only" in args:
        i = args.index("--only")
        if i + 1 >= len(args):
            sys.exit(__doc__)
        only = set(args[i + 1].split(","))
        del args[i:i + 2]
        unknown = only - {sid for sid, _, _ in SLIDES}
        if unknown:
            sys.exit(f"unknown slide ids: {', '.join(sorted(unknown))}")

    mode = args[0] if args else ""
    if mode not in ("", "--audio-only", "--render-only") or len(args) > 1:
        sys.exit(__doc__)

    if mode == "--render-only":
        entries = json.loads(MANIFEST.read_text())["slides"]
    else:
        entries = synthesize(clone_ref, only)

    if mode != "--audio-only":
        render()
        print(f"\nwrote {OUT_MP4}  ({OUT_MP4.stat().st_size / 1e6:.1f} MB)")

    total = sum(LEAD_IN + e["seconds"] + TAIL for e in entries)
    if len(entries) != len(SLIDES):
        # Chapter marks are cumulative, so a partial run would write a
        # description whose timings are wrong for every chapter after the gap.
        print(f"partial: {len(entries)}/{len(SLIDES)} slides, "
              f"{int(total // 60)}:{int(total % 60):02d} so far; description not written")
        return
    write_description(entries)
    print(f"wrote {HERE / 'description.txt'}  (runtime {int(total // 60)}:{int(total % 60):02d})")


if __name__ == "__main__":
    main()
