import { empty, falsee, len, truee } from 'choo'

function bcdiff (past, next) {
  if (typeof next == 'string') {
    next = next.split(empty)
  }
  if (typeof past == 'string') {
    past = past.split(empty)
  }
  if (next.toString() == past.toString()) {
    return [0]
  }

  function wood (next) {

    function trie (i, j, kf, leaf) {
      const a = next[++kf]
      if (typeof leaf == 'number') {
        const b = next[++leaf]
        const leaves = {}
        if (a == b) {
          leaves[b] = trie(i, j, kf, leaf)
        } else {
          leaves[a] = i
          leaves[b] = j
        }
        return leaves
      } else if (typeof leaf == 'object') {
        leaf[a] = a in leaf ? trie(i, leaf[a], kf, leaf[a]) : i
        return leaf
      }
    }

    const tree = {}
    for (let a, b, branch, i = 0, leaf, length = len(next); i < length; i++) {
      a = next[i]
      b = next[i + 1]
      if (a in tree) {
        branch = tree[a]
        if (b in branch) {
          leaf = branch[b]
          branch[b] = {...trie(i, leaf, i, leaf)[b], ...leaf}
        } else {
          branch[b] = i
        }
      } else {
        branch = {}
        branch[b] = i
      }
      tree[a] = branch
    }
    return tree
  }

  const tree = wood(next)

  function overlaps (a, b) {
    let i = 0, length = len(a)
    while (i < length && a[i] == b[i]) {
      i++
    }
    return i
  }

  function brs (branches, bs) {
    for (let branch of branches) {
      if (typeof branch == 'number') {
        bs.push(branch)
      } else {
        bs = brs(Object.values(branch), bs)
      }
    }
    return bs
  }

  function abs (a) {
    return a < 0 ? -a : a
  }

  function matches (branch, stick, i, j=0) {
    let leaf = stick[j]
    if (leaf in branch) {
      leaf = branch[leaf]
      if (typeof leaf == 'number') {
        i = overlaps(next.slice(leaf), stick)
        if (i > 2) {
          return [leaf, i]
        }
      } else if (typeof leaf == 'object') {
        return matches(leaf, stick, i, j + 1)
      }
    } else if (j > 2) {
      const bs = brs(Object.values(branch), [])
      let b, c = -1
      for (b of bs) {
        if (c == -1 || abs(b - i) < c) {
          branch = b
          c = abs(b - i)
        }
      }
      return [branch, overlaps(next.slice(branch), stick)]
    }
    return falsee
  }

  function position (list, sublist, j=0) {
    if (len(sublist) == 0) {
      return j
    }
    for (let a = sublist[0], i = 0, l = len(list), m = len(sublist); i < l; i++) {
      if (list[i] === a) {
        return position(list.slice(i + 1, i + m), sublist.slice(1), j ? j : i)
      }
    }
    return -1
  }

  function checks (best, branch, buffer, leaf) {
    if (typeof leaf == 'object') {
      let e = Object.keys(leaf)
      for (let f of e) {
        if (branch[0] == f) {
          let g, h, i, j
          g = leaf[f]
          h = branch.concat(f)
          i = 1
          j = h[i]
          while (typeof g == 'object' && j in g) {
            g = g[j]
            h.push(j)
            i++
            j = h[i]
          }
          if (i > 3 && i > (best[3] | 0)) {
            best = []
          }
        }
        best = checks(best, branch.concat(f), buffer, leaf[f])
      }
    }
    return best
  }

  function reps (buffer) {
    const b = wood(buffer.slice(2))
    let best = [], i = 0, leaf
    for (leaf of Object.keys(b)) {
      best = checks(best, buffer, [leaf], b[leaf], i++)
    }
    return best
  }

  function comp (a, b) {
    let c = reps(a)
    let d = c[3]
    if (d >= 3) {
      const e = ['c', b + len(c[0]) + 2, ...c[0], c[1]]
      c = c[2]
      if (c >= 3) {
        a[1] = c - 2
        e.unshift(...comp(a.slice(0, c), b))
      }
      c += d
      d = len(a)
      if (c < d) {
        e.push(...comp(['c', d - c, ...a.slice(c)], b))
      }
      return e
    }
    a[0] = 'a'
    a[1] += b + 2
    return a
  }

  let f = [], i = 0, l, length = len(past), match, p = [], patch = [], pos, q = 0
  while (i < length) {
    match = matches(tree, past.slice(i), i)
    if (match) {
      l = len(f)
      if (l) {
        pos = position(next, f)
        if (pos >= 0) {
          patch.push(pos, l)
          p.push(q += 2)
        } else {
          patch.push('a', l, ...f)
          p.push(q += 2 + l)
        }
        f = []
      }
      pos = match[0]
      match = match[1]
      patch.push(pos, match)
      p.push(q += 2)
      i += match
    } else {
      f.push(past[i++])
    }
  }
  l = len(f)
  if (l) {
    patch.push('a', l, ...f)
    p.push(q += 2 + l)
  }
  let a, as = {}, g = [], h, j, k, m, ps = []
  for (i of p) {
    if (patch[i] == 'a') {
      a = i + 2
      f = patch.slice(a, a + patch[i + 1])
      j = 0
      l = len(f)
      m = []
      while ((j = patch.indexOf(f[0], j + 1)) != -1) {
        if (a != j && f.toString() == patch.slice(j, j + l).toString()) {
          m.push(j)
        }
      }
      if (len(m) == 0) {
        patch[i] = 'c'
        ps.push(i)
      } else {
        l = -1
        for (j of m) {
          h = j - 2
          k = falsee
          if (patch[j] == 'a') {
            k = truee
          } else if (patch[h] > l || i == j && patch[h] == l) {
            k = truee
            l = patch[h]
            h = a + patch[i + 1]
            while (i <= h) {
              g.push(h--)
            }
          }
          if (k) {
            if (i in as) {
              as[i].push([j, patch[i + 1]])
            } else {
              as[i] = [[j, patch[i + 1]]]
            }
          }
        }
      }
    }
  }
  let b, c, d, e
  const bs = {}, cs = {}, es = {}
  i = 0, j = 0, length = len(patch), p = []
  while (i < length) {
    b = i
    c = j
    cs[i] = j + 1
    while (b-- > 0 && !(b in cs)) {
      cs[b] = c--
    }
    b = falsee
    if (i in as) {
      c = -1
      d = as[i]
      for (a of d) {
        e = a[0]
        if (g.indexOf(e) == -1 && (c == -1 || abs(e - i) < c) && (e < i || patch[a[0] - 2] != 'a')) {
          b = a
          c = abs(e - i)
        }
      }
    }
    if (b) {
      c = b[0] - 3
      if (ps.indexOf(c) > -1) {
        es[i] = c
        f = ['e', c, 1, patch[i + 1] + 1]
      } else {
        bs[i] = b[0]
        f = ['b', ...b]
        g.push(i + 2)
      }
      i += len(patch.slice(i, i + 2 + patch[i + 1]))
    } else {
      b = patch[i]
      c = patch[i + 1]
      if (b == 'a') {
        f = patch.slice(i, i += c + 2)
        f[1] += j + 2
      } else if (b == 'c') {
        f = patch.slice(i, i += c + 2)
        f = comp(f, j)
      } else {
        f = [a = b, a + c]
        i += 2
      }
    }
    j += len(f)
    p.push(...f)
  }
  for (b in bs) {
    p[a = cs[b]] = c = cs[bs[b] - 1]
    p[a + 1] += c
  }
  for (e in es) {
    p[cs[e]] = cs[es[e] - 1]
  }
  return p
}

function bcpatch (last, p) {
  let b, c, d, i = 0, l = len(p), past = []
  if (l == 1) {
    return [...last.slice(p[0])]
  }

  function bc (a) {
    if (typeof a == 'number') {
      return last.slice(a, p[i++])
    } else if (a == 'a') {
      a = p[i++]
      return p.slice(i, i = a)
    } else if (a == 'b') {
      return p.slice(p[i++], p[i++])
    } else if (a == 'c') {
      a = p[i++]
      b = a - i
      b = p.slice(i, i = a, a = b)
      return Array(p[i++]).fill().map((i, c) => b[c % a])
    } else if (a == 'd') {
      a = p[i++]
      b = a - i
      b = p.slice(i, i = a, a = b)
      c = last.slice(c = p[i++], d = p[i++], d -= c)
      return Array(p[i++]).fill().map((i, e) => b[e % a] + c[e % d])
    } else if (a == 'e') {
      a = i
      i = p[i++]
      b = bc(p[i++])
      i = a + 1
      return b.slice(p[i++], p[i++])
    }
    return []
  }

  while (i < l) {
    past.push(...bc(p[i++]))
  }
  return past
}

function avcs () {

  function uint8 (a) {
    return new Uint8Array(a)
  }

  function uint32 (a) {
    return new Uint32Array(a)
  }

  function uint32_t (a) {
    return uint32([a])[0]
  }

  function bytebits (a) {
    let b = 0, c = len(a), d = []
    while (b < c) {
      d.push(a[b++] ^ a[b++] << 1 ^ a[b++] << 2 ^ a[b++] << 3 ^ a[b++] << 4 ^ a[b++] << 5 ^ a[b++] << 6 ^ a[b++] << 7)
    }
    return uint8(d)
  }

  function bytebytes (a) {
    let b = 0, c = len(a), d = [], e, f = 255, g = 0, h = 1
    while (b < c) {
      e = a[b++]
      if (e > g) {
        g = e
      }
      d.push(e & f, e >> 8 & f, e >> 16 & f, e >> 24 & f)
    }
    while (uint32_t(g /= 256) > 0) {
      h++
    }
    d = d.filter((a, b) => b % 4 < h)
    if (len(d)) {
      d.unshift(h)
    }
    return uint8(d)
  }

  function bytenums (a) {
    let b = 0, c = len(a), d = [], e, f = 255
    while (b < c) {
      e = a[b++]
      d.push(e & f, e >> 8 & f, e >> 16 & f, e >> 24 & f)
    }
    return uint8(d)
  }

  function base (a) {
    return new TextEncoder().encode(a)
  }

  function sabe (a) {
    return new TextDecoder().decode(a)
  }

  function lengths (a) {
    let b, c = []
    while (len(a) > 0) {
      b = [...a.slice(0, 4)]
      a = a.slice(4)
      while (b[len(b) - 1] == 0) {
        b.pop()
      }
      c.push(b)
    }
    return c
  }

  this.encode = function (patch) {
    let bits = [], lens = [], nums = [], strs = []
    for (let i = 0, length = len(patch), p; i < length; i++) {
      p = patch[i]
      if (typeof p == 'number') {
        bits.push(0)
        nums.push(p)
      } else if (typeof p == 'string') {
        bits.push(1)
        strs.push(p)
      }
    }
    bits = bytebits(bits)
    nums = bytebytes(uint32(nums))
    lens = lengths(bytenums([len(bits), len(nums)]))
    strs = base(strs.join(empty))
    const leng = len(lens[0]) + 4 * len(lens[1])
    return uint8([leng, ...lens[0], ...lens[1], ...bits, ...nums, ...strs])
  }

  function bitbytes (a) {
    let b = 0, c = len(a), d = [], e, f = 1
    while (b < c) {
      e = a[b++]
      d.push(e & f, e >> 1 & f, e >> 2 & f, e >> 3 & f, e >> 4 & f, e >> 5 & f, e >> 6 & f, e >> 7 & f)
    }
    return d
  }

  function bytesbytes (a) {
    let b = 1, c = len(a), d = [], e, f, g = a[0]
    while (b < c) {
      e = 0, f = 0
      while (f < g) {
        e ^= a[b++] << f++ * 8
      }
      d.push(e)
    }
    return d
  }

  function number (a) {
    let b = 0, c = len(a), d = 0
    while (b < c) {
      d ^= a[b] << (8 * b++)
    }
    return d
  }

  this.decode = function (bytes) {
    let b = 0
    let len0 = bytes[b++]
    let len1 = uint32_t(len0 / 4)
    len0 = number(bytes.slice(b, b += len0 % 4))
    len1 = number(bytes.slice(b, b += len1))
    const bits = bitbytes(bytes.slice(b, b += len0))
    const nums = bytesbytes(bytes.slice(b, b += len1))
    const strs = sabe(bytes.slice(b))
    const patch = []
    for (let i = 0, j = 0, k = 0, l = len(nums) + len(strs); i < l;) {
      patch.push(bits[i++] == 0 ? nums[j++] : strs[k++])
    }
    return patch
  }

  function random (bytes=1) {
    if (bytes > 65536) {
      return [...random(65536), ...random(bytes - 65536)]
    }
    return crypto.getRandomValues(uint8(bytes))
  }

  function string (a) {
    return btoa(String.fromCharCode(...a))
  }

  this.encrypt = function (patch) {
    const length = len(patch)
    const rand = random(length)
    for (let i = 0; i < length; i++) {
      patch[i] ^= rand[i]
    }
    return [string(patch), string(rand)]
  }

  function bytes (a) {
    return Uint8Array.from(atob(a), a => a.charCodeAt())
  }

  this.decrypt = function (patch, rand) {
    patch = bytes(patch)
    rand = bytes(rand)
    for (let i = 0, length = len(patch); i < length; i++) {
      patch[i] ^= rand[i]
    }
    return patch
  }

  this.diff = function (past, next, bytes=truee, encrypt=truee) {
    let patch = bcdiff(past, next)
    if (bytes || encrypt) {
      patch = this.encode(patch)
    }
    return encrypt ? this.encrypt(patch) : patch
  }

  this.patch = function (last, patch, bytes=truee, encrypt=truee) {
    if (encrypt) {
      patch = this.decrypt(patch[0], patch[1])
    }
    if (bytes || encrypt) {
      patch = this.decode(patch)
    }
    const past = bcpatch(last, patch)
    return typeof last == 'string' ? past.join(empty) : past
  }

}