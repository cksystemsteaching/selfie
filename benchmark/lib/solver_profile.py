from dataclasses import dataclass, field
from typing import NewType, NamedTuple, Dict, List

Timestamp = NewType("Timestamp", float)
MegaBytes = NewType("MegaBytes", int)
CPUPercent = NewType("CPUPercent", float)


class ProfileSample(NamedTuple):
    """Timestamped measurement of all solver runtime metrics"""

    timestamp: Timestamp
    rss: MegaBytes
    cpu_percent: CPUPercent


@dataclass
class SolverProfiler:
    samples: Dict["Model", List[ProfileSample]] = field(default_factory=dict)

    def record_sample(
        self, model: "Model", timestamp: float, rss: int, cpu_percent: float
    ):
        """Record a new performance sample with current timestamp"""
        self.samples.setdefault(model, []).append(
            ProfileSample(
                timestamp=Timestamp(timestamp),
                rss=MegaBytes(rss),
                cpu_percent=CPUPercent(cpu_percent),
            )
        )

    # Analysis methods
    def peak_memory(self, model: "Model") -> MegaBytes | None:
        """Get maximum RSS observed"""
        if samples := self.samples.get(model):
            return max(s.rss for s in samples)
        return None
