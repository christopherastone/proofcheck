class Item:
    def __init__(self, cat, sem, why=None):
        self.cat = cat
        self.sem = sem
        self.why = why

    def __str__(self):
        print("cat:", str(self.cat), repr(self.cat))
        return f'({self.cat},{self.sem})'

    def __repr__(self):
        return f'Item({self.cat!r},{self.sem!r},{self.why!r})'

    def __eq__(self, other):
        """ignores the why argument, and checks sem for pointer equality"""
        return self.cat == other.cat and self.sem == other.sem

    def toStrings(self):
        if isinstance(self.why, str):
            lines = [self.why]
        elif isinstance(self.why, list):
            reason = self.why[0]
            extra = 1+len(reason)
            leftLines = self.why[1].toStrings()
            rightLines = self.why[2].toStrings() if len(self.why) >= 2 else []
            lines = Item.mergeLines(leftLines, rightLines, extra)
            lines += ['-' * (len(lines[0])-extra) + ' ' + reason]
        else:
            lines = ["???"]
        lines += [str(self.cat)]
        lines += [str(self.sem)]
        return Item.centerlines(lines)

    @staticmethod
    def centerlines(lines):
        width = max(len(l) for l in lines)
        return [' ' * ((width-len(l)) // 2) + l + ' ' * ((width+1-len(l)) // 2)
                for l in lines]

    @staticmethod
    def mergeLines(lines1, lines2, extra=0):
        len1 = len(lines1)
        wid1 = len(lines1[0])
        len2 = len(lines2)
        wid2 = len(lines2[0])
        minlen = min(len1, len2)
        rmargin = ' ' * extra
        part1 = [lines1[i] + '  ' + lines2[i] + rmargin
                 for i in range(minlen)]
        part2 = [' ' * (wid1+2) + lines2[i] + rmargin
                 for i in range(minlen, len2)]
        part3 = [lines1[i] + '  ' * (wid2+2) + rmargin
                 for i in range(minlen, len1)]
        return part1 + part2 + part3

    def display(self):
        for l in self.toStrings():
            print(l)
