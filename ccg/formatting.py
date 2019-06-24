def center_lines(lines):
    """Given a list of lines, center the lines relative to the longest.
        The resulting strings are all the same length, since they will
        be space-padded on both sides."""
    width = max(len(l) for l in lines)
    return [' ' * ((width-len(l)) // 2) + l + ' ' * ((width+1-len(l)) // 2)
            for l in lines]


def merge_lines(lines1, lines2):
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
