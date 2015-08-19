local    smt = setmetatable
local   type = type
local  error = error
local  pcall = pcall
local select = select

local min, max = math.min, math.max

local        s = string
local     srep = s.rep
local     ssub = s.sub
local    sgsub = s.gsub
local    sfind = s.find
local    sbyte = s.byte
local    schar = s.char
local   smatch = s.match
local  sgmatch = s.gmatch
local sreverse = s.reverse

local   table = table
local tconcat = table.concat

local E = function(...) error(..., 3) end
--local E = function(...) return nil, ... end

-- Patterns
local pattern = (function(...)
    local mt

    local function new(p, t, a, e)
      return smt({p = p, t = t, a = a, e = e}, mt)
    end

    -- upper lower replace table
    -- e.g. ulrt['A'] = 'a', ulrt['a'] = 'A'
    local ulrt = {}
    for x,y in sgmatch("abcdefghijklmnopqrstuvwxyz", "()(.)") do
      local z = ssub("ABCDEFGHIJKLMNOPQRSTUVWXYZ",x,x)
      ulrt[y] = z
      ulrt[z] = y
    end

    mt = {
      __concat = function(a, b)
        if b.a then
          return E("Pattern cannot be prepended to")
        end
        if a.e then
          return E("Pattern cannot be appended to")
        end
        return new(a.p .. b.p, min(a.t, b.t), a.a, b.e)
      end,
      __tostring = function(t)
        return t.p
      end,
      __mul = function(t, n)
        return new(srep(t.p), 2, t.a, t.e)
      end,
      __add = function(t, q)
        if sfind("+-?*", q, 1, true) and t.t > 2 then
          return new(t.p .. "+", 2, t.a, t.e)
        else
          return E("Not quantifiable or invalid quantifier")
        end
      end,
      __index = {
        find = function(t, s, n)
          return sfind(s, (t.a or "") .. t.p .. (t.e or ""), n or 1)
        end,
        gsub = function(t, s, r, n)
          return sgsub(s, (t.a or "") .. t.p .. (t.e or ""), r, n or 1)
        end,
        gmatch = function(t, s)
          return sgmatch(s, (t.a or "") .. t.p .. (t.e or ""))
        end,
        match = function(t, s, n)
          return smatch(s, (t.a or "") .. t.p .. (t.e or ""), n or 1)
        end,
      },
      __unm = function(t)
        if #t.p == 2 and ssub(t.p,1,1) == "%" and ulrt[ssub(t.p,2,2)] then
          return new("%" .. ulrt[ssub(t.p,2,2)], t.t, t.a, t.e)
        else
          return t
        end
      end,
      __eq = function(a, b)
        return a.p == b.p and a.t == b.t and a.a == b.a and a.e == b.e
      end
    }

    local function escape(s)
      return sgsub(s, "%W", "%%%0")
    end

    local function str(s)
      return new(escape(s), 2)
    end

    local function raw(s)
      local a, e
      if ssub(s,1,1) == "^" then a = "^" end
      if ssub(s,-1,-1) == "$" then e = "$" end
      return new(s, 1, a, e)
    end

    local function group(p)
      if p.t < 2 then
        return E("Pattern may contain ungroupable characters")
      end
      if #p.p == 0 then
        -- HACK: always captures an empty string
        return new("([\2-\1]?)", 2)
      end
      return new("(" .. p.p .. ")", 2)
    end

    local function escaperange_helper(c)
      -- NOT NEEDED as `.` doesn't need escaping inside `[]`
      -- if c == "." then return false end
      local s, r = pcall(smatch, c, c)
      return s and r == c
    end
    local function escaperange(l, u)
      local t1 = {}
      local n1 = 1
      local last1
      for i=sbyte(l), sbyte(u) do
        if escaperange_helper(schar(i)) then
          last1 = i
          break
        end
        t1[n1] = escape(schar(i))
        n1 = n1 + 1
      end
      if last1 then
        local t2 = {}
        local n2 = 1
        local last2
        for i=sbyte(u), last1, -1 do
          if escaperange_helper(schar(i)) then
            last2 = i
            break
          end
          t2[n2] = escape(schar(i))
          n2 = n2 + 1
        end
        local middle = ""
        if last1 ~= last2 then middle = schar(last1) .. "-" .. schar(last2) end
        return tconcat(t1, "")  .. middle .. sreverse(tconcat(t2, ""))
      else
        return tconcat(t1, "")
      end
    end

    local function set(...)
      local t, n
      local negate
      if ... == false or ... == true then
        t = {select(2, ...)}
        n = select('#', ...) - 1
        -- set(true, ...) should be "in set", set(false, ...) should be "not in set"
        -- it's more intuitive this way
        negate = not ...
      else
        t = {...}
        n = select('#', ...)
      end

      if n == 0 then return E("Set cannot be empty") end

      for i=1, n do
        local v = t[i]
        if type(v) == "string" then
          local l = #v
          if l == 1 then
            t[i] = escape(v)
          elseif l == 2 or l == 3 then
            local lbound, ubound = ssub(v,1,1), ssub(v,2,2)
            if l == 3 then
              if ubound ~= "-" then
                return E("Not a range")
              end
              ubound = ssub(v,3,3)
              v = lbound .. ubound
              l = #v
            end
            t[i] = escaperange(lbound, ubound)
          else
            return E("Not a character or range")
          end
        elseif type(v) == "table" then
          if v.t < 4 then
            return E("Not a character")
          end
          t[i] = v.p
        else
          return E("Not a character or range")
        end
      end
      return new((negate and "[^" or "[") .. tconcat(t, "") .. "]", 3)
    end

    local function frontier(s)
      if ssub(s.p,1,1) == "[" and ssub(s.p,-1,-1) == "]" then
        return new("%f" .. s.p, 2)
      else
        return E("Not a set")
      end
    end

    local function bpairs(a,b)
      if #a == 1 and #b == 1 then
        return new("%b" .. a .. b, 2)
      else
        return E("Not a character")
      end
    end

    local function character(c)
      if #c ~= 1 then return E("Not a character") end
      return new(escape(c), 4)
    end

    local quantifiers = {
      ["+"] = "+",
      ["-"] = "-",
      ["*"] = "*",
      ["?"] = "?",
      ["1+"] = "+",
      ["0+"] = "*",
      optional = "?",
      ["shortest0+"] = "-",
      nongreedy = "-",
      shortest = "-",
    }
    local function quantify(t, q)
      local qt = quantifiers[q]
      if qt and t.t > 2 then
        return new(t.p .. qt, 2)
      else
        return E("Not quantifiable")
      end
    end
    mt.__index.quantify = quantify

    local presets = {
      any = new(".", 3),
      letter = new("%a", 3),
      control = new("%c", 3),
      digit = new("%d", 3),
      printable_no_space = new("%g", 3),
      lowercase = new("%l", 3),
      punctuation = new("%p", 3),
      space = new("%s", 3),
      uppercase = new("%u", 3),
      alphanumeric = new("%w", 3),
      hexadecimal = new("%x", 3),
      startwith = new("", 1, "^"),
      endwith = new("", 1, nil, "$"),
      pos = new("()", 2),
    }

    return {
      raw = raw,
      str = str,
      group = group,
      set = set,
      character = character,
      frontier = frontier,
      bpairs = bpairs,
      presets = presets
    }
  end)(...)

-- Structs
local struct = (function(...)
    local mt = {}
    -- TODO
  end)(...)

return {pattern = pattern, struct = struct}