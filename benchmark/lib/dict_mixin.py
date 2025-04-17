from dataclasses import asdict
from typing import Any, Dict
import json

import threading
from dataclasses import asdict
import json
from typing import Dict, Any

class DictMixin:
    """Enables dictionary access"""
    def _ensure_initialized(self): pass

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