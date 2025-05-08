"""
Predefined color palettes for consistent visualization across BT's graphing tools.
All colors are optimized for readability and colorblind accessibility.

Note: This is an internal utility class used exclusively by the grapher module.
"""


class ColorMap:
    # Primary colors
    PRIMARY = {
        "blue": "#3574C6",  # Vibrant but not overwhelming
        "red": "#E64A3C",  # For highlights/important data
        "green": "#4EAC5B",  # Balanced mid-tone
        "purple": "#7E57C2",  # Good contrast to blues
        "orange": "#FF8F3E",  # For secondary elements
    }

    # Extended categorical palette (8 colors)
    QUALITATIVE = [
        "#3574C6",  # Blue
        "#E64A3C",  # Red
        "#4EAC5B",  # Green
        "#7E57C2",  # Purple
        "#FF8F3E",  # Orange
        "#5FB7D4",  # Cyan
        "#F06292",  # Pink
        "#8D6E63",  # Brown
    ]

    # Sequential (for ordered data)
    SEQUENTIAL = [
        "#F7FBFF",  # Lightest
        "#D2E3F3",
        "#9ECAE1",
        "#6BAED6",
        "#3B8EC9",
        "#1E6DB7",  # Darkest
    ]

    # Diverging (for variance from median)
    DIVERGING = [
        "#D7191C",  # Negative
        "#FDAE61",
        "#FFFFBF",  # Neutral
        "#ABD9E9",
        "#2C7BB6",  # Positive
    ]

    SOLVER = {
        "z3": "#F06292",        # Pink
        "bitwuzla": "#5FB7D4",  # Cyan
    }
