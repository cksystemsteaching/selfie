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

# Improved LazyLoadedDictMixin
class LazyLoadedDictMixin(DictMixin):
    """Extends DictMixin with thread-safe lazy initialization using __getattr__."""

    def __init__(self):
        self._is_initialized = False
        self._init_lock = threading.Lock()

    def _ensure_initialized(self):
        """Triggers initialization thread-safely if not already done."""
        if not self._is_initialized:
            with self._init_lock:
                if not self._is_initialized:
                    try:
                        self._initialize()
                    except Exception as e:
                        # Optional: Handle initialization errors appropriately
                        # Depending on requirements, you might want to reset
                        # _is_initialized or re-raise a specific exception.
                        print(f"Error during initialization: {e}")
                        raise
                    self._is_initialized = True

    def _initialize(self):
        """Override this in subclasses to implement loading logic.
        This method should set the attributes that will be accessed lazily.
        """
        print("Performing initialization...")
        # Example: Load data and set attributes
        # self.data = load_heavy_data()
        # self.computed_value = compute_something_expensive()
        pass # Replace with actual initialization

    def __getattr__(self, name: str) -> Any:
        """Handles access to missing attributes by triggering initialization."""
        # Avoid recursion on special attributes if accessed via __getattr__
        # (less likely than with __getattribute__, but good practice)
        if name in {'_is_initialized', '_init_lock', '_initialize', '_ensure_initialized'}:
             # Should ideally not happen if accessed correctly, raise error
             raise AttributeError(f"'{type(self).__name__}' object has no attribute '{name}' (internal access attempted via __getattr__)")

        # Ensure initialized *before* trying to access the attribute
        self._ensure_initialized()

        try:
            # After initialization, the attribute should exist.
            # Use object.__getattribute__ to bypass our own __getattr__
            # if accessing the attribute directly might re-trigger it (though less likely here).
            # Alternatively, getattr(self, name) might suffice if _initialize guarantees creation.
            return object.__getattribute__(self, name)
        except AttributeError:
            # If _initialize didn't create the attribute, raise the error.
            raise AttributeError(f"'{type(self).__name__}' object has no attribute '{name}' after initialization") from None

    # Override methods from DictMixin that might access attributes before __getattr__ is triggered
    def __getitem__(self, key: str) -> Any:
        """Dictionary access with lazy loading."""
        try:
             # Try direct access first (might be already initialized and present)
             # Use object.__getattribute__ to avoid triggering __getattr__ if key is not yet set
             return object.__getattribute__(self, key)
        except AttributeError:
             # If direct access fails, trigger __getattr__ logic
             # This will call _ensure_initialized and then try to get the attribute again
             return self.__getattr__(key)

    # to_dict and pretty_print in DictMixin already call _ensure_initialized,
    # but ensure they work correctly after initialization sets attributes.