import React from 'react';
import {Composition} from 'remotion';
import manifest from './narration.json';
import {Explainer, totalDurationInFrames} from './Explainer';

export const RemotionRoot: React.FC = () => (
  <Composition
    id="Explainer"
    component={Explainer}
    durationInFrames={totalDurationInFrames}
    fps={manifest.fps}
    width={1920}
    height={1080}
  />
);
