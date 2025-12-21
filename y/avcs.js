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

  function pick (branches, leafs) {
    for (let branch of branches) {
      if (typeof branch == 'object') {
        leafs = pick(Object.values(branch), leafs)
      } else {
        leafs.push(branch)
      }
    }
    return leafs
  }

  function abs (a) {
    return a < 0 ? -a : a
  }

  const leng = len(next)

  function overlap (a, b, ai, bi) {
    let i = 0, l = leng - ai
    while (i < l && a[ai + i] == b[bi + i]) {
      i++
    }
    if (i > 2) {
      return [ai, i]
    }
    return falsee
  }

  function matches (branch, stick, i, j=0) {
    let leaf = branch[stick[i + j]]
    if (leaf) {
      if (typeof leaf == 'object') {
        return matches(leaf, stick, i, j + 1)
      } else {
        return overlap(next, stick, leaf, i)
      }
    } else if (j > 0) {
      const bs = pick(Object.values(branch), [])
      let b, c = bs[0] + i + 1
      for (b of bs) {
        if (abs(b - i) < c) {
          leaf = b
          c = abs(b - i)
        }
      }
      return overlap(next, stick, leaf, i)
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

  function get (best, branch, buffer, leaf, p) {
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
        best = get(best, branch.concat(f), buffer, leaf[f], p)
      }
    }
    return best
  }

  function reps (buffer) {
    const b = wood(buffer)
    let best = [], i = 0, leaf
    for (leaf in b) {
      best = get(best, [leaf], buffer, b[leaf], i++)
    }
    return best
  }

  function comp (buffer, pos) {
    let c = reps(buffer.slice(2))
    if (len(c)) {
      let d = c[0]
      let e = c[2] + c[3]
      const f = ['c', d + pos + 2, ...c[1], e]
      if (d) {
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

  let f = [], i = 0, j = 0, l = len(past), m, match, p = [], patch = [], pos
  while (i < l) {
    match = matches(trie, past, i)
    if (match) {
      m = len(f)
      if (m) {
        pos = position(next, f)
        if (pos >= 0) {
          patch.push(pos, m)
          p.push(j += 2)
        } else {
          patch.push('a', m, ...f)
          p.push(j += m + 2)
        }
        f = []
      }
      pos = match[0]
      match = match[1]
      patch.push(pos, match)
      p.push(j += 2)
      i += match
    } else {
      f.push(past[i++])
    }
  }
  m = len(f)
  if (m) {
    patch.push('a', m, ...f)
    p.push(j += m + 2)
  }
  let a, b, c, d, e, g, h, k
  const as = {}, cs = [], gs = []
  for (i of p) {
    if (patch[i] == 'a') {
      a = 0
      b = i + 2
      f = patch[i + 1]
      g = new Array(f)
      while (a < f) {
        g[a] = patch[a++ + b]
      }
      a = 0
      f = []
      h = g[0]
      j = len(g)
      while ((a = patch.indexOf(h, a + 1)) != -1) {
        if (a != b) {
          k = 0
          while (j > k) {
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
          } else if (patch[h] > g || patch[h] == g && a == i) {
            g = patch[h]
            h = b + patch[i + 1]
            while (i <= h) {
              gs.push(h--)
            }
            j = truee
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
  i = 0, j = 0, l = len(patch), p = []
  while (i < l) {
    a = i
    b = j
    ps[i] = j + 1
    while (a-- && !(a in ps)) {
      ps[a] = b--
    }
    a = falsee
    if (i in as) {
      b = l
      c = as[i]
      for (d of c) {
        e = d[0]
        if (gs.indexOf(e) == -1 && abs(e - i) < b && (e < i || patch[e - 2] != 'a')) {
          a = d
          b = abs(e - i)
        }
      }
    }
    if (a && !a) {
      b = a[0] - 3
      if (cs.indexOf(b) > -1) {
        es[i] = b
        f = ['e', b, 1, patch[i + 1] + 1]
        j += 4
      } else {
        bs[i] = a[0]
        f = ['b', a[0], a[1]]
        gs.push(i + 2)
        j += 3
      }
      i += patch[i + 1] + 2
    } else {
      a = patch[i]
      b = patch[i + 1]
      c = 2
      if (a == 'a') {
        c += b
        f = patch.slice(i, i += c)
        f[1] += j + 2
      } else if (a == 'c') {
        c += b
        f = patch.slice(i, i += c)
        f[0] = 'a'
        f[1] += j + 2
      } else {
        f = [a, a + b]
        i += c
      }
      j += c
    }
    p.push(...f)
  }
  for (b in bs) {
    a = ps[b]
    b = ps[bs[b] - 1]
    p[a] = b
    p[a + 1] += b
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
    let b = 0, c = len(a), d = [], e, f
    while (b < c) {
      e = 0
      f = 0
      while (e < 5 && b < c) {
        f += a[b++] * 3 ** e++
      }
      d.push(f)
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
    let b = 0, c = len(a), d = [], e
    while (b < c) {
      e = [...a.slice(b, b += 4)]
      while (e[len(e) - 1] == 0) {
        e.pop()
      }
      d.push(e)
    }
    return d
  }

  this.encode = function (a) {
    let len0 = 0, len1 = 0, len2 = 0
    let bytes = [], leng = [], lens = [], nums = [], sits = [], strs = [], trits = []
    for (let i = 0, l = len(a), p; i < l; i++) {
      p = a[i]
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
    leng = bytebytes([len(lens[0]) + len(lens[1]) * 4 + len(lens[2]) * 16 + len(lens[3]) * 64])
    leng = len(leng) == 1 ? [leng[0], 0] : leng
    lens = [...lens[0], ...lens[1], ...lens[2], ...lens[3]]
    return [...leng, ...lens, ...sits, ...trits, ...bytes, ...nums, ...base(strs.join(empty))]
  }

  function bytesbytes (a) {
    let b = 1, c = len(a), d = [], e, f, g = a[0]
    while (b < c) {
      e = 0
      f = 0
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

  function tritsbytes (a) {
    let b = 0, c = len(a), d = [], e, f
    while (b < c) {
      e = 0
      f = a[b++]
      while (e++ < 5) {
        d.push(f % 3)
        f = uint8_t(f / 3)
      }
    }
    return d
  }

  this.decode = function (a) {
    let b = 0
    let len0 = bytesbytes(a.slice(b, b += 2))
    let len1 = uint8_t(len0 / 4)
    let len2 = uint8_t(len0 / 16)
    let len3 = uint8_t(len0 / 64)
    len0 = number(a.slice(b, b += len0 % 4))
    len1 = number(a.slice(b, b += len1 % 4))
    len2 = number(a.slice(b, b += len2 % 4))
    len3 = number(a.slice(b, b += len3 % 4))
    const sits = bytesbytes(a.slice(b, b += len0))
    const trits = tritsbytes(a.slice(b, b += len1))
    const bytes = a.slice(b, b += len2)
    const nums = bytesbytes(a.slice(b, b += len3))
    const strs = sabe(a.slice(b))
    a = []
    b = len(sits)
    let c = 0, d = 0, e = 0, f = 0
    while (c < b) {
      if (trits[c] == 0) {
        a.push(...bytes.slice(d, d += sits[c++]))
      } else if (trits[c] == 1) {
        a.push(...nums.slice(e, e += sits[c++]))
      } else {
        a.push(...strs.slice(f, f += sits[c++]))
      }
    }
    return a
  }

  function random (a) {
    if (a > 65536) {
      return [...random(65536), ...random(a - 65536)]
    }
    return crypto.getRandomValues(uint8(a))
  }

  function string (a) {
    if (len(a) > 65535) {
      return string(a.slice(0, 65535)) + string(a.slice(65535))
    }
    return btoa(String.fromCharCode(...a))
  }

  this.encrypt = function (patch) {
    const l = len(patch)
    const rand = random(l)
    for (let i = 0; i < l; i++) {
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
    for (let i = 0, l = len(patch); i < l; i++) {
      patch[i] ^= rand[i]
    }
    return patch
  }

  this.diff = function (past, next, encrypt=truee, encode=falsee) {
    let patch = bcdiff(past, next)
    let check = bcpatch(next, patch)
    if (typeof past == 'string') {
      check = check.join(empty)
    }
    if (check.toString() != past.toString()) {
      console.error('bad diff', patch)
      throw 'bad patch'
    }
    if (encode || encrypt) {
      patch = this.encode(patch)
    }
    return encrypt ? this.encrypt(patch) : patch
  }

  this.patch = function (last, patch, encrypt=truee, encode=falsee) {
    if (encrypt) {
      patch = this.decrypt(patch[0], patch[1])
    }
    if (encode || encrypt) {
      patch = this.decode(patch)
    }
    const past = bcpatch(last, patch)
    return typeof last == 'string' ? past.join(empty) : past
  }

}