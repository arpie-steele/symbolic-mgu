#!/usr/bin/env python3
"""
Sort and deduplicate .cargo/lingo.dic spell-checker dictionary.

Preserves the first line (word count) and sorts all other lines
in a case-insensitive, human-friendly order while removing duplicates.
"""

import sys
from pathlib import Path


def sort_dictionary(filepath: Path) -> None:
    """Sort and deduplicate dictionary file."""
    # Read all lines
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    if not lines:
        print("Error: Empty file", file=sys.stderr)
        sys.exit(1)

    # First line is the word count (we'll recalculate it)
    header = lines[0].strip()

    # Rest are dictionary words - strip whitespace and filter empty lines
    words = [line.strip() for line in lines[1:] if line.strip()]

    # Remove duplicates while preserving order
    # (use dict to maintain insertion order)
    seen = {}
    unique_words = []
    for word in words:
        if len(word) < 1:
            continue
        if word.endswith("’s"):
            word = word[:-2] + "'s"
        if word.endswith("/SM"):
            word = word[:-3] + "/MS"
        key = (word
               if word.find(" ") != -1
               or word.isascii() and (len(word) > 1 and word[:3].isupper()
                                      or not (word.islower()
                                              or word.isupper())) else
               word.lower())
        if key not in seen:
            seen[key] = True
            unique_words.append(word)

    # Sort case-insensitively (but preserve original case in output)
    sorted_words = sorted(unique_words, key=lambda s: ((0 if s.isascii() else 2) + (0 if s[0].isalnum() else 4) + (0 if s.isalnum() else 2), s.casefold(), s.lower()))

    # Update count
    new_count = len(sorted_words)
    new_header = 50 * int((new_count + 65) // 50)

    # Write back
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(f"{new_header}\n")
        for word in sorted_words:
            f.write(f"{word}\n")

    # Report changes
    original_count = len(words)
    duplicates_removed = original_count - new_count

    print(f"Dictionary sorted and deduplicated:")
    print(f"  Original entries: {original_count}")
    print(f"  Unique entries:   {new_count}")
    print(f"  Duplicates removed: {duplicates_removed}")

    if header != str(new_header):
        print(f"  Warning: Header count was '{header}', now {new_count}")


def main():
    """Main entry point."""
    if len(sys.argv) > 1:
        filepath = Path(sys.argv[1])
    else:
        # Default to .cargo/lingo.dic in project root
        script_dir = Path(__file__).parent
        project_root = script_dir.parent
        filepath = project_root / ".cargo" / "lingo.dic"

    if not filepath.exists():
        print(f"Error: File not found: {filepath}", file=sys.stderr)
        sys.exit(1)

    sort_dictionary(filepath)


if __name__ == "__main__":
    main()
