import { empty, falsee, len, truee } from 'choo'

function bcdiff (past, next) {
  if (typeof past == 'string') {
    past = past.split(empty)
  }
  if (typeof next == 'string') {
    next = next.split(empty)
  }
  if (past.toString() == next.toString()) {
    return [0]
  }

  function wood (next) {

    function order (i, j, kf, leaf) {
      const a = next[++kf]
      if (typeof leaf == 'number') {
        const b = next[++leaf]
        const leaves = {}
        if (a == b) {
          leaves[b] = order(i, j, kf, leaf)
        } else {
          leaves[a] = i
          leaves[b] = j
        }
        return leaves
      } else if (typeof leaf == 'object') {
        leaf[a] = a in leaf ? order(i, leaf[a], kf, leaf[a]) : i
        return leaf
      }
    }

    const trie = {}
    for (let a, b, branch, i = 0, leaf, l = len(next); i < l; i++) {
      a = next[i]
      b = next[i + 1]
      if (a in trie) {
        branch = trie[a]
        if (b in branch) {
          leaf = branch[b]
          branch[b] = {...order(i, leaf, i, leaf)[b], ...leaf}
        } else {
          branch[b] = i
        }
      } else {
        branch = {}
        branch[b] = i
      }
      trie[a] = branch
    }
    return trie
  }

  const trie = wood(next)

  function abs (a) {
    return a < 0 ? -a : a
  }

  const leng = len(next)

  function overlaps (a, b, ai, bi) {
    let i = 0, l = leng - ai
    while (i < l && a[ai + i] == b[bi + i]) {
      i++
    }
    return i
  }

  function pick (branches, leafs) {
    for (let branch of branches) {
      if (typeof branch == 'number') {
        leafs.push(branch)
      } else {
        leafs = pick(Object.values(branch), leafs)
      }
    }
    return leafs
  }

  function matches (branch, stick, i, j=0) {
    let leaf = branch[stick[i + j]]
    if (leaf) {
      type = typeof leaf
      if (type == 'number') {
        i = overlaps(next, stick, leaf, i)
        if (i > 2) {
          return [leaf, i]
        }
      } else if (type == 'object') {
        return matches(leaf, stick, i, j + 1)
      } else {
      }
    } else if (j > 2) {
      const bs = pick(Object.values(branch), [])
      let b, c = -1
      for (b of bs) {
        if (c == -1 || abs(b - i) < c) {
          branch = b
          c = abs(b - i)
        }
      }
      return [branch, overlaps(next, stick, branch, i)]
    }
    return falsee
  }

  function position (list, sublist, j=0, k=0, l=len(sublist)) {
    const m = l - k
    if (m == 0) {
      return j
    }
    for (let a = sublist[k], i = 0, l = len(list); i < l; i++) {
      if (list[i] === a) {
        return position(list.slice(i + 1, i + m), sublist, j ? j : i, k++, l)
      }
    }
    return -1
  }

  function checks (best, branch, buffer, leaf, p) {
    if (typeof leaf == 'object') {
      let f, g, h, i, j
      for (f in leaf) {
        if (branch[0] == f) {
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
          g = len(branch)
          if (i > 3 && (i > (best[2] | 0) || (i == best[2] && g < best[3]))) {
            best = [p, branch, i, g]
          }
        }
        best = checks(best, branch.concat(f), buffer, leaf[f], p)
      }
    }
    return best
  }

  function reps (buffer) {
    const b = wood(buffer)
    let best = [], i = 0, leaf
    for (leaf in b) {
      best = checks(best, [leaf], buffer, b[leaf], i++)
    }
    return best
  }

  function comp (buffer, pos) {
    let c = reps(buffer.slice(2))
    if (len(c)) {
      let d = c[0]
      let e = c[2] + c[3]
      const f = ['c', d + pos + 2, ...c[1], e]
      if (d > 0) {
        buffer[1] = d
        f.unshift(...comp(buffer.slice(0, d + 2), pos))
      }
      d += e
      e = len(buffer)
      if (d < e) {
        f.push(...comp(['c', d - e, buffer.slice(d)], d + pos))
      }
      return f
    }
    buffer[0] = 'a'
    buffer[1] += pos + 2
    return buffer
  }

  let f = [], i = 0, l, m = len(past), match, p = [], patch = [], pos, q = 0
  while (i < m) {
    match = matches(trie, past, i)
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
  let a, b, c, d, e, g, h, j, k
  const as = {}, cs = [], gs = []
  for (i of p) {
    if (patch[i] == 'a') {
      a = 0
      b = i + 2
      f = patch[i + 1]
      g = new Array(f)
      h = 0
      while (h < f) {
        g[h] = patch[b + h++]
      }
      f = []
      h = g[0]
      j = len(g)
      while ((a = patch.indexOf(h, a + 1)) != -1) {
        if (a != b) {
          k = 0
          while (k < j) {
            if (g[k] != patch[a + k++]) {
              k = 0
              break
            }
          }
          if (k) {
            f.push(a)
          }
        }
      }
      if (len(f) == 0) {
        cs.push(i)
        patch[i] = 'c'
      } else {
        g = -1
        for (a of f) {
          h = a - 2
          j = falsee
          if (patch[a] == 'a') {
            j = truee
          } else if (patch[h] > g || a == i && patch[h] == g) {
            j = truee
            g = patch[h]
            h = b + patch[i + 1]
            while (i <= h) {
              gs.push(h--)
            }
          }
          if (j) {
            if (i in as) {
              as[i].push([a, patch[i + 1]])
            } else {
              as[i] = [[a, patch[i + 1]]]
            }
          }
        }
      }
    }
  }
  const bs = {}, es = {}, ps = {}
  i = 0, j = 0, m = len(patch), p = []
  while (i < m) {
    b = i
    c = j
    ps[i] = j + 1
    while (b-- > 0 && !(b in ps)) {
      ps[b] = c--
    }
    b = falsee
    if (i in as) {
      c = -1
      d = as[i]
      for (a of d) {
        e = a[0]
        if (gs.indexOf(i + 2) == -1 && (c == -1 || abs(e - i) < c) && (e < i || patch[a[0] - 2] != 'a')) {
          b = a
          c = abs(e - i)
        }
      }
    }
    if (falsee) {
      c = b[0] - 3
      if (cs.indexOf(c) > -1) {
        es[i] = c
        f = ['e', c, 1, patch[i + 1] + 1]
      } else {
        bs[i] = b[0]
        f = ['b', b[0], b[1]]
        gs.push(i + 2)
      }
      i += len(patch.slice(i, i + patch[i + 1] + 2))
    } else {
      b = patch[i]
      c = patch[i + 1]
      if (b == 'a') {
        f = patch.slice(i, i += c + 2)
        f[1] += j + 2
      } else if (b == 'c') {
        f = patch.slice(i, i += c + 2)
        f[0] = 'a'
        f[1] += j + 2
      } else {
        f = [a = b, b + c]
        i += 2
      }
    }
    j += len(f)
    p.push(...f)
  }
  for (b in bs) {
    p[a = ps[b]] = c = ps[bs[b] - 1]
    p[a + 1] += c
  }
  for (e in es) {
    p[ps[e]] = ps[es[e] - 1]
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

  function uint8_t (a) {
    return uint8([a])[0]
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
    while ((g /= 256) >= 1) {
      h++
    }
    d = d.filter((a, b) => b % 4 < h)
    if (len(d)) {
      d.unshift(h)
    }
    return d
  }

  function bytenums (a) {
    let b = 0, c = len(a), d = [], e, f = 255
    while (b < c) {
      e = a[b++]
      d.push(e & f, e >> 8 & f, e >> 16 & f, e >> 24 & f)
    }
    return d
  }

  function bytetrits (a) {
    let b = 0, c = len(a), d = [], e = 5, f, g
    while (b < c) {
      f = 0
      g = 0
      while (f < e) {
        if (b + f < c) {
          g += a[b + f] * (3 ** f)
        }
        f++
      }
      b += e
      d.push(g)
    }
    return d
  }

  function base (a) {
    return new TextEncoder().encode(a)
  }

  function sabe (a) {
    return new TextDecoder().decode(a)
  }

  function lengths (a) {
    let b, c = []
    while (len(a)) {
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
    let len0 = 0, len1 = 0, len2 = 0
    let sits = [], bytes = [], leng = [], lens = [], nums = [], strs = [], trits = []
    for (let i = 0, l = len(patch), p; i < l; i++) {
      p = patch[i]
      if (typeof p == 'number') {
        if (p < 256) {
          bytes.push(p)
          len0++
          if (len1) {
            sits.push(len1)
            len1 = 0
            trits.push(1)
          } else if (len2) {
            sits.push(len2)
            len2 = 0
            trits.push(2)
          }
        } else {
          nums.push(p)
          len1++
          if (len0) {
            sits.push(len0)
            len0 = 0
            trits.push(0)
          } else if (len2) {
            sits.push(len2)
            len2 = 0
            trits.push(2)
          }
        }
      } else if (typeof p == 'string') {
        strs.push(p)
        len2++
        if (len0) {
          sits.push(len0)
          len0 = 0
          trits.push(0)
        } else if (len1) {
          sits.push(len1)
          len1 = 0
          trits.push(1)
        }
      }
    }
    if (len0) {
      sits.push(len0)
      trits.push(0)
    } else if (len1) {
      sits.push(len1)
      trits.push(1)
    } else {
      sits.push(len2)
      trits.push(2)
    }
    sits = bytebytes(sits)
    trits = bytetrits(trits)
    nums = bytebytes(nums)
    lens = lengths(bytenums([len(sits), len(trits), len(bytes), len(nums)]))
    strs = base(strs.join(empty))
    leng = bytebytes([len(lens[0]) + len(lens[1]) * 4 + len(lens[2]) * 16 + len(lens[3]) * 64])
    lens = [...lens[0], ...lens[1], ...lens[2], ...lens[3]]
    return [len(leng), ...leng, ...lens, ...sits, ...trits, ...bytes, ...nums, ...strs]
  }

  function tritsbytes (a) {
    let b = 0, c = len(a), d = [], e, f
    while (b < c) {
      e = a[b++]
      f = 0
      while (f < 5) {
        d.push(e % 3)
        e = uint8_t(e / 3)
        f++
      }
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
      d ^= a[b] << b++ * 8
    }
    return d
  }

  this.decode = function (p) {
    let b = 0
    let len0 = p[b++]
    len0 = bytesbytes(p.slice(b, b += len0))
    let len1 = uint8_t(len0 / 4)
    let len2 = uint8_t(len0 / 16)
    let len3 = uint8_t(len0 / 64)
    len0 = number(p.slice(b, b += len0 % 4))
    len1 = number(p.slice(b, b += len1 % 4))
    len2 = number(p.slice(b, b += len2 % 4))
    len3 = number(p.slice(b, b += len3 % 4))
    const types = bytesbytes(p.slice(b, b += len0))
    const trits = tritsbytes(p.slice(b, b += len1))
    const bytes = p.slice(b, b += len2)
    const nums = bytesbytes(p.slice(b, b += len3))
    const strs = sabe(p.slice(b))
    const patch = []
    let i = 0, j = 0, k = 0, l = 0, m = len(types)
    while (i < m) {
      if (trits[i] == 0) {
        patch.push(...bytes.slice(j, j += types[i++]))
      } else if (trits[i] == 1) {
        patch.push(...nums.slice(k, k += types[i++]))
      } else {
        patch.push(...strs.slice(l, l += types[i++]))
      }
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
    if (len(a) > 65535) {
      return string(a.slice(0, 65535)) + string(a.slice(65535))
    }
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

  this.diff = function (past, next, encrypt=truee, bytes=falsee) {
    let patch = bcdiff(past, next)
    if (bcpatch(next, patch).toString() != past.toString()) {
      console.error('bad diff', patch)
      throw new Error('bad patch')
    }
    if (bytes || encrypt) {
      patch = this.encode(patch)
    }
    return encrypt ? this.encrypt(patch) : patch
  }

  this.patch = function (last, patch, encrypt=truee, bytes=falsee) {
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