from dataclasses import asdict
from typing import Any, Dict
import json


class DictMixin:
    """
    Mixin class that provides dictionary-like access to dataclass attributes.
    Enables conversion to dict and pretty-printing while maintaining type safety.

    Typical usage:
        @dataclass
        class MyData(DictMixin):
            field: str

        data = MyData("value")
        data["field"]  # Dictionary access
        data.to_dict()  # Convert to plain dict
    """

    def _ensure_initialized(self):
        pass

    def __getitem__(self, key):
        return getattr(self, key)

    def get(self, key, default=None):
        try:
            return self[key]
        except (KeyError, AttributeError):
            return default

    def to_dict(self) -> Dict[str, Any]:
        self._ensure_initialized()
        return asdict(self)

    def pretty_print(self) -> str:
        return json.dumps(self.to_dict(), indent=2, default=str)
