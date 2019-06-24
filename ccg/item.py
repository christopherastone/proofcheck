"""Representation of a [partial] parse."""

import formatting
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

    # def subst(self, sub):
    #     cat2 = self.cat.subst(sub)
    #     sem2 = self.sem
    #     why2 = self.why
    #     if (isinstance(self.why, list)):
    #         why2 = [x.subst(sub) if isinstance(x, Item) else x
    #                 for x in self.why
    #                 ]
    #     else:
    #         why2 = self.why
    #     return Item(cat2, sem2, why2)

    def display(self):
        """Prints the parse as a pretty tree"""
        for l in self.toStrings():
            print(l)

    def toStrings(self):
        """Returns lines containing a pretty-print of this
           parse as a tree. An important (recursive) invariant of this
           code is that all lines will have the same length
           (space padded, if necessary)"""

        bottom_lines = [str(self.cat), str(self.cat.semty), str(self.sem)]

        if isinstance(self.why, str):
            # This is just a single input word. Report the
            #   category and semantics (which came from the lexicon).
            lines = [self.why] + bottom_lines
            return formatting.center_lines(lines)

        elif isinstance(self.why, list):
            # This is a unary, binary, etc. rule application
            rule_label = self.why[0]
            rule_width = len(rule_label)

            justifications = [item.toStrings() for item in self.why[1:]]

            top_lines = functools.reduce(
                formatting.merge_lines, justifications)
            top_width = max(len(l) for l in top_lines)

            bottom_width = max(len(l) for l in bottom_lines)

            MINIMUM_RULE_LENGTH = 4
            rule_length = max(MINIMUM_RULE_LENGTH, top_width, bottom_width)
            rule_line = '-' * rule_length

            lines = formatting.center_lines(
                top_lines + [rule_line] + bottom_lines)

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
        lines = ["???"] + bottom_lines
        return formatting.centerlines(lines)

    def rule(self):
        """Return the rule name from the 'why' part, if any"""
        if isinstance(self.why, list):
            return self.why[0]
        else:
            return ''
