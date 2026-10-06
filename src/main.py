import re
import sys
from array import array


KEEP, DEL, INS = 61, 45, 43  # ord('='), ord('-'), ord('+')

# Maximum number of V entries kept for backtracking.
# 4 bytes each when stored as array('i').
TRACE_BUDGET = 30_000_000


# ============================================================
# Myers diff - trace version
# ============================================================

def _myers_trace(a, b):
    """
    Myers O(ND) diff with V history.

    Returns an edit script:
        '=' -> keep
        '-' -> delete
        '+' -> insert

    Returns None if the trace would exceed TRACE_BUDGET.
    """
    n, m = len(a), len(b)

    if n == 0:
        return b'+' * m
    if m == 0:
        return b'-' * n

    max_d = n + m
    off = max_d + 1

    v = [0] * (2 * max_d + 3)
    trace = []

    used = 0
    final_d = -1

    for d in range(max_d + 1):

        for k in range(-d, d + 1, 2):

            # Decide whether to insert or delete.
            if k == -d or (
                k != d and
                v[off + k - 1] < v[off + k + 1]
            ):
                # Insert from B.
                x = v[off + k + 1]
            else:
                # Delete from A.
                x = v[off + k - 1] + 1

            y = x - k

            # Snake: keep matching elements for free.
            while x < n and y < m and a[x] == b[y]:
                x += 1
                y += 1

            v[off + k] = x

            if x >= n and y >= m:
                final_d = d
                break

        if final_d >= 0:
            break

        used += d + 1

        if used > TRACE_BUDGET:
            return None

        row = v[off - d:off + d + 1]

        if used < 1_000_000:
            trace.append(row)
        else:
            trace.append(array('i', row))

    # --------------------------------------------------------
    # Backtrack
    # --------------------------------------------------------

    ops = bytearray()

    x, y = n, m

    for d in range(final_d, 0, -1):

        vp = trace[d - 1]
        o = d - 1
        k = x - y

        if k == -d or (
            k != d and
            vp[o + k - 1] < vp[o + k + 1]
        ):
            # Came from insertion.
            pk = k + 1
            px = vp[o + pk]
            mx = px
            edit = INS

        else:
            # Came from deletion.
            pk = k - 1
            px = vp[o + pk]
            mx = px + 1
            edit = DEL

        # Snake after the edit.
        ops.extend(b'=' * (x - mx))

        ops.append(edit)

        x = px
        y = px - pk

    # Initial snake.
    ops.extend(b'=' * x)

    ops.reverse()

    return bytes(ops)


# ============================================================
# Myers linear-space fallback
# ============================================================

def _middle_snake(a, alo, ahi, b, blo, bhi):
    """
    Find a middle snake for the linear-space version of Myers.
    """

    n = ahi - alo
    m = bhi - blo

    delta = n - m
    odd = delta & 1

    max_d = (n + m + 1) // 2

    off = max_d + abs(delta) + 2

    vf = [0] * (2 * off + 1)
    vb = [0] * (2 * off + 1)

    for d in range(max_d + 1):

        # Forward search
        for k in range(-d, d + 1, 2):

            if k == -d or (
                k != d and
                vf[off + k - 1] < vf[off + k + 1]
            ):
                x = vf[off + k + 1]
            else:
                x = vf[off + k - 1] + 1

            y = x - k

            sx, sy = x, y

            while (
                x < n and
                y < m and
                a[alo + x] == b[blo + y]
            ):
                x += 1
                y += 1

            vf[off + k] = x

            if odd and delta - (d - 1) <= k <= delta + (d - 1):
                if x + vb[off + delta - k] >= n:
                    return sx, sy, x, y

        # Backward search
        for k in range(-d, d + 1, 2):

            if k == -d or (
                k != d and
                vb[off + k - 1] < vb[off + k + 1]
            ):
                x = vb[off + k + 1]
            else:
                x = vb[off + k - 1] + 1

            y = x - k

            sx, sy = x, y

            while (
                x < n and
                y < m and
                a[ahi - 1 - x] == b[bhi - 1 - y]
            ):
                x += 1
                y += 1

            vb[off + k] = x

            if not odd and -d <= delta - k <= d:
                if x + vf[off + delta - k] >= n:
                    return (
                        n - x,
                        m - y,
                        n - sx,
                        m - sy
                    )

    raise AssertionError("no middle snake")


def _myers_linear(a, b):
    """
    Linear-space Myers diff using the middle-snake technique.
    """

    out = bytearray()

    def rec(alo, ahi, blo, bhi):

        # Common prefix.
        while (
            alo < ahi and
            blo < bhi and
            a[alo] == b[blo]
        ):
            out.append(KEEP)
            alo += 1
            blo += 1

        # Common suffix.
        suf = 0

        while (
            ahi > alo and
            bhi > blo and
            a[ahi - 1] == b[bhi - 1]
        ):
            ahi -= 1
            bhi -= 1
            suf += 1

        # Nothing left in A.
        if alo == ahi:
            out.extend(b'+' * (bhi - blo))

        # Nothing left in B.
        elif blo == bhi:
            out.extend(b'-' * (ahi - alo))

        else:
            sx, sy, ex, ey = _middle_snake(
                a, alo, ahi,
                b, blo, bhi
            )

            rec(
                alo,
                alo + sx,
                blo,
                blo + sy
            )

            out.extend(b'=' * (ex - sx))

            rec(
                alo + ex,
                ahi,
                blo + ey,
                bhi
            )

        out.extend(b'=' * suf)

    rec(0, len(a), 0, len(b))

    return bytes(out)


# ============================================================
# General Myers wrapper
# ============================================================

def _core(a, b):
    ops = _myers_trace(a, b)

    if ops is None:
        ops = _myers_linear(a, b)

    return ops


# ============================================================
# Pre-processing
# ============================================================

def _middle(am, bm):

    if not am:
        return b'+' * len(bm)

    if not bm:
        return b'-' * len(am)

    sa = set(am)
    sb = set(bm)

    ia = [
        i for i, value in enumerate(am)
        if value in sb
    ]

    ib = [
        j for j, value in enumerate(bm)
        if value in sa
    ]

    # Everything can potentially match.
    if len(ia) == len(am) and len(ib) == len(bm):
        return _core(am, bm)

    # No possible matches.
    if not ia:
        return (
            b'-' * len(am) +
            b'+' * len(bm)
        )

    # Remove elements that can never match anything
    # on the other side.
    filtered_a = [am[i] for i in ia]
    filtered_b = [bm[j] for j in ib]

    fops = _core(filtered_a, filtered_b)

    out = bytearray()

    i = j = 0
    p = q = 0

    for op in fops:

        if op == KEEP:

            ti = ia[p]
            tj = ib[q]

            out.extend(b'-' * (ti - i))
            out.extend(b'+' * (tj - j))

            out.append(KEEP)

            i = ti + 1
            j = tj + 1
            p += 1
            q += 1

        elif op == DEL:

            ti = ia[p]

            out.extend(
                b'-' * (ti - i + 1)
            )

            i = ti + 1
            p += 1

        else:

            tj = ib[q]

            out.extend(
                b'+' * (tj - j + 1)
            )

            j = tj + 1
            q += 1

    out.extend(b'-' * (len(am) - i))
    out.extend(b'+' * (len(bm) - j))

    return bytes(out)


def diff_ops(a, b):
    """
    Return minimal edit script of two sequences.

    '=' -> keep
    '-' -> delete
    '+' -> insert
    """

    n = len(a)
    m = len(b)

    # Common prefix.
    pre = 0

    while (
        pre < n and
        pre < m and
        a[pre] == b[pre]
    ):
        pre += 1

    # Common suffix.
    suf = 0

    while (
        suf < n - pre and
        suf < m - pre and
        a[n - 1 - suf] == b[m - 1 - suf]
    ):
        suf += 1

    mid = _middle(
        a[pre:n - suf],
        b[pre:m - suf]
    )

    return (
        b'=' * pre +
        mid +
        b'=' * suf
    )


# ============================================================
# Delete-first rule
# ============================================================

_BLOCK = re.compile(rb'[-+]+')


def _delete_first(match):
    block = match.group()

    deletes = block.count(b'-')
    inserts = block.count(b'+')

    return (
        b'-' * deletes +
        b'+' * inserts
    )


def line_ops(a, b):
    """
    Run Myers on lines and enforce:
        all '-' before all '+' inside a change block.
    """

    return _BLOCK.sub(
        _delete_first,
        diff_ops(a, b)
    )


# ============================================================
# Part B - character highlighting
# ============================================================

def _ranges_text(marks):
    """
    Convert positions into:
        3-5,9-12

    If nothing changed:
        .
    """

    if not marks:
        return '.'

    parts = []

    start = marks[0]
    prev = marks[0]

    for p in marks[1:]:

        if p != prev + 1:
            parts.append(
                f'{start}-{prev + 1}'
            )

            start = p

        prev = p

    parts.append(
        f'{start}-{prev + 1}'
    )

    return ','.join(parts)


def highlight_line(old, new):
    """
    Find changed character ranges between one
    deleted line and one inserted line.
    """

    old_text = old.decode(
        'utf-8',
        'surrogateescape'
    )

    new_text = new.decode(
        'utf-8',
        'surrogateescape'
    )

    old_marks = []
    new_marks = []

    i = 0
    j = 0

    for op in diff_ops(old_text, new_text):

        if op == KEEP:
            i += 1
            j += 1

        elif op == DEL:
            old_marks.append(i)
            i += 1

        else:
            new_marks.append(j)
            j += 1

    result = (
        '? ' +
        _ranges_text(old_marks) +
        ' | ' +
        _ranges_text(new_marks) +
        '\n'
    )

    return result.encode('utf-8')


# ============================================================
# Input
# ============================================================

def read_lines(path):
    """
    Read file as raw bytes.

    Split only on b'\\n'.
    Keep b'\\r' as part of the line.
    """

    with open(path, 'rb') as f:
        data = f.read()

    lines = data.split(b'\n')

    # Final newline does not create an extra line.
    if lines[-1] == b'':
        lines.pop()

    return lines


# ============================================================
# Output
# ============================================================

def render(a, b, ops, with_highlight):
    """
    Write output in chunks to avoid keeping the
    complete diff in memory.
    """

    i = 0
    j = 0

    pending = []

    pair = 0

    chunks = []
    CHUNK_SIZE = 8192

    def flush():
        if chunks:
            sys.stdout.buffer.write(
                b''.join(chunks)
            )
            chunks.clear()

    for op in ops:

        if op == KEEP:

            chunks.append(
                b' ' + a[i] + b'\n'
            )

            i += 1
            j += 1

            pending.clear()
            pair = 0

        elif op == DEL:

            pending.append(a[i])

            chunks.append(
                b'-' + a[i] + b'\n'
            )

            i += 1

        else:

            chunks.append(
                b'+' + b[j] + b'\n'
            )

            # Pair the first '-' with the first '+',
            # second '-' with second '+', etc.
            if (
                with_highlight and
                pair < len(pending)
            ):
                chunks.append(
                    highlight_line(
                        pending[pair],
                        b[j]
                    )
                )

            pair += 1
            j += 1

        if len(chunks) >= CHUNK_SIZE:
            flush()

    flush()


# ============================================================
# Main
# ============================================================

def main(argv):

    if (
        len(argv) != 4 or
        argv[1] not in ('lines', 'highlight')
    ):
        sys.stderr.write(
            'usage: main.py lines|highlight A B\n'
        )
        return 2

    try:
        a = read_lines(argv[2])
        b = read_lines(argv[3])

    except OSError as e:
        sys.stderr.write(
            f'error: {e}\n'
        )
        return 2

    # Convert identical byte strings to integer IDs.
    # This makes comparisons cheaper for the Myers algorithm.
    ids = {}

    ia = [
        ids.setdefault(value, len(ids))
        for value in a
    ]

    ib = [
        ids.setdefault(value, len(ids))
        for value in b
    ]

    ops = line_ops(ia, ib)

    try:
        render(
            a,
            b,
            ops,
            argv[1] == 'highlight'
        )

        sys.stdout.buffer.flush()

    except BrokenPipeError:
        pass

    return 0


if __name__ == '__main__':
    sys.setrecursionlimit(10000)
    sys.exit(main(sys.argv))
