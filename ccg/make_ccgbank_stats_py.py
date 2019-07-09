#! /usr/bin/env python3

# ./make_ccgbank_stats_py.py
# ./make_ccgbank_stats_py.py data/ccgbank_1_1/data/LEX/CCGbank.00-24.lexicon

import catparser
import collections
import sys


def process_lexicon(filename, MIN_COUNT=50):
    print(f'starting read for {filename}')
    cat_dict = collections.defaultdict(list)
    with open(filename, 'r') as file:
        for line in file:
            values = line.split()
            assert len(values) == 5
            word = values[0]
            cat = values[1]
            count = int(values[2])
            if cat == '.':
                continue
            if count < MIN_COUNT:
                continue
            cat_dict[cat].append((count, word))
    print(f'done.')
    summarize(cat_dict)


def summarize(cat_dict, NUM_WORDS=5, NUM_CATS=30):
    cats = sorted(cat_dict.keys(), key=lambda x: len(x))
    print(f'{len(cats)} categories.')
    for cat in cats[:NUM_CATS]:
        words = cat_dict[cat]
        top_N_words = sorted(words)[:NUM_WORDS]
        print('\t'.join([cat] + [w for _, w in top_N_words]))


if __name__ == '__main__':
    if len(sys.argv) == 2 and sys.argv[1].endswith('.lexicon'):
        filename = sys.argv[1]
    elif len(sys.argv) == 1:
        filename = 'data/ccgbank_1_1/data/LEX/CCGbank.00-24.lexicon'
    else:
        print(f'usage: {sys.argv[0]} <lexicon file>')
        exit(-1)

    process_lexicon(filename)
