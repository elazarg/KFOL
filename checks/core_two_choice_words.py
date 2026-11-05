"""Reduce two-choice translation words by first-occurrence phases.

Tokens identify fixed translations. Each phase starts when a previously
unseen token occurs. Within a phase retain only its first occurrences.
The appendix proves that each deletion preserves the transformation;
this is a bounded representative, not a uniqueness claim.
"""


def normalize(word):
    seen = set()
    phase = set()
    result = []
    for token in word:
        if token not in seen:
            seen.add(token)
            phase = set()
        if token not in phase:
            phase.add(token)
            result.append(token)
    return tuple(result)
