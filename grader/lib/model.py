from dataclasses import dataclass
from typing import Callable, Optional, List

@dataclass(frozen=True)
class CheckResult:
    result: bool
    msg: str
    output: str
    warning: str
    should_succeed: bool = True
    command: Optional[str] = None
    mandatory: bool = False

@dataclass(frozen=True)
class Check:
    msg: str
    command: str
    execute: Callable[[], CheckResult]

@dataclass(frozen=True)
class Assignment:
    name: str
    lecture: str
    category: str
    description: str
    create_checks: Callable[[], List[Check]]

    def __hash__(self):
        return hash(self.name)
