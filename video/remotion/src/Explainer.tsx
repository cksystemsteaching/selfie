import React from 'react';
import {AbsoluteFill, Audio, Img, Sequence, interpolate, staticFile, useCurrentFrame} from 'remotion';
import manifest from './narration.json';

const {fps, leadInSeconds, tailSeconds} = manifest;

// The deck's own ground colour, so the letterbox around a still is invisible.
const GROUND = '#080E18';

// How long a build step takes to fade in. The stills are cumulative -- each
// one is the slide with one more fragment revealed -- so a step fading in over
// its predecessor reads as that fragment appearing, which is what the deck
// does live.
const FADE = 0.42;

export const slideDurationInFrames = (narrationSeconds: number): number =>
  Math.round((leadInSeconds + narrationSeconds + tailSeconds) * fps);

export const totalDurationInFrames = manifest.slides.reduce(
  (sum, s) => sum + slideDurationInFrames(s.seconds),
  0
);

const Slide: React.FC<{steps: {image: string; at: number}[]}> = ({steps}) => {
  const frame = useCurrentFrame();
  return (
    <AbsoluteFill style={{backgroundColor: GROUND}}>
      {steps.map((step, i) => {
        // Step 0 is already on screen when the slide arrives: it carries the
        // heading, and fading that in would look like a stutter after the
        // slide itself has just faded in.
        const start = (leadInSeconds + step.at) * fps;
        const opacity =
          i === 0
            ? 1
            : interpolate(frame, [start - FADE * fps * 0.35, start + FADE * fps * 0.65], [0, 1], {
                extrapolateLeft: 'clamp',
                extrapolateRight: 'clamp',
              });
        return (
          <AbsoluteFill key={step.image} style={{opacity}}>
            <Img src={staticFile(step.image)} style={{width: '100%', height: '100%'}} />
          </AbsoluteFill>
        );
      })}
    </AbsoluteFill>
  );
};

export const Explainer: React.FC = () => {
  let from = 0;
  return (
    <AbsoluteFill style={{backgroundColor: GROUND}}>
      {manifest.slides.map((s) => {
        const dur = slideDurationInFrames(s.seconds);
        const seq = (
          <Sequence key={s.id} from={from} durationInFrames={dur}>
            <Slide steps={s.steps} />
            <Sequence from={Math.round(leadInSeconds * fps)}>
              <Audio src={staticFile(`audio/${s.id}.wav`)} />
            </Sequence>
          </Sequence>
        );
        from += dur;
        return seq;
      })}
    </AbsoluteFill>
  );
};
