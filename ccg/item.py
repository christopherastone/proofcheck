"""Representation of a [partial] parse."""

import functools


class Item:
    """
         .cat is the category of the parse
         .sem is the semantics of the parse
         .why is the rule that constructed the item
                 (a list containing the rule name followed by
                  the input items --- unless it corresponds
                  to a single input word, in which case it's that
                  string.)
    """

    def __init__(self, cat, sem, why=None):
        self.cat = cat
        self.sem = sem
        self.why = why

    def __str__(self):
        """Nice but compact representation of the category & semantics"""
        return f'({self.cat},{self.sem})'

    def __repr__(self):
        """String representation of an item"""
        return f'Item({self.cat!r},{self.sem!r},{self.why!r})'

    def __eq__(self, other):
        """Item equality.
           Warning: ignores the why argument, and currently the
           semantic check is doing pointer equality."""
        return self.cat == other.cat and self.sem == other.sem

    def display(self):
        """Prints the parse as a pretty tree"""
        for l in self.toStrings():
            print(l)

    def toStrings(self):
        """Returns lines containing a pretty-print of this
           parse as a tree. An important (recursive) invariant of this
           code is that all lines will have the same length
           (space padded, if necessary)"""
        if isinstance(self.why, str):
            # This is just a single input word. Report the
            #   category and semantics (which came from the lexicon).
            lines = [self.why,
                     str(self.cat),
                     str(self.sem)]
            return Item.centerlines(lines)

        if isinstance(self.why, list):
            # This is a unary, binary, etc. rule application
            rule_label = self.why[0]
            rule_width = len(rule_label)

            justifications = [item.toStrings() for item in self.why[1:]]

            top_lines = functools.reduce(Item.mergeLines, justifications)
            top_width = max(len(l) for l in top_lines)

            bottom_lines = [str(self.cat), str(self.sem)]
            bottom_width = max(len(l) for l in bottom_lines)

            MINIMUM_RULE_LENGTH = 4
            rule_length = max(MINIMUM_RULE_LENGTH, top_width, bottom_width)
            rule_line = '-' * rule_length

            lines = Item.centerlines(top_lines + [rule_line] + bottom_lines)

            # Add justification, keeping all lines the same length
            out = []
            rmargin = ' ' + ' ' * rule_width
            for line in lines:
                if line == rule_line:
                    out += [line + ' ' + rule_label]
                else:
                    out += [line + rmargin]
            return out

        # If we got this far, there was no valid justification
        lines = ["???", str(self.cat), str(self.sem)]
        return Item.centerlines(lines)

    @staticmethod
    def centerlines(lines):
        """Given a list of lines, center the lines relative to the longest.
           The resulting strings are all the same length, since they will
           be space-padded on both sides."""
        width = max(len(l) for l in lines)
        return [' ' * ((width-len(l)) // 2) + l + ' ' * ((width+1-len(l)) // 2)
                for l in lines]

    @staticmethod
    def mergeLines(lines1, lines2):
        """Merges the given lines into a single "two-column" format.
           Assumes all the lines in a list have the same fixed length
             (though the two lists can have different fixed lengths)
        """
        len1 = len(lines1)
        wid1 = len(lines1[0]) if len1 > 0 else 0
        len2 = len(lines2)
        wid2 = len(lines2[0]) if len2 > 0 else 0
        minlen = min(len1, len2)

        # All the output where we can take lines from both lists
        part1 = [lines1[i] + '  ' + lines2[i] for i in range(minlen)]
        # Non-empty if the second list was longer
        part2 = [' ' * (wid1+2) + lines2[i] for i in range(minlen, len2)]
        # Non-empty if the first list was longer
        part3 = [lines1[i] + ' ' * (wid2+2) for i in range(minlen, len1)]

        return part1 + part2 + part3
