/-  Copyright (C) 2023 The OpenAPI library contributors.

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
-/

import Http
import Lean

open Lean

/- TODO: move all these things to Http -/

namespace Http

inductive StatusCodeRange
| default
| range (n : Nat)
| exact (s : Http.StatusCode)

def StatusCode.ofNat! (n : Nat) : Http.StatusCode :=
  if h1 : _ then
    if h2 : _ then
      ⟨⟨n,h1⟩,h2⟩
    else panic! s!"Http.StatusCode.ofNat!: {n} is not a status code"
  else panic! s!"Http.StatusCode.ofNat!: {n} is not a status code"

instance : Quote Http.StatusCode where
  quote | s => Syntax.mkCApp ``Http.StatusCode.ofNat! #[quote s.val.toNat]

instance : Quote StatusCodeRange where
  quote
  | .default => Syntax.mkCApp ``StatusCodeRange.default #[]
  | .range n => Syntax.mkCApp ``StatusCodeRange.range #[quote n]
  | .exact s => Syntax.mkCApp ``StatusCodeRange.exact #[quote s]

def StatusCodeRange.ofString (s : String) : Option StatusCodeRange :=
  if s = "default" then
    some .default
  else if s.length != 3 then
    none
  else if (s.get 0).isDigit &&
          s.get ⟨1⟩ == 'X' &&
          s.get ⟨2⟩ == 'X' then
    some <| .range <| (s.get 0).toNat - '0'.toNat
  else
    s.toNat? |>.bind (fun n =>
      if h1 : _ then
        if h2 : _ then
          some <| .exact ⟨⟨n, h1⟩, h2⟩
        else none
      else none
    )

def StatusCodeRange.matches : StatusCodeRange → Http.StatusCode → Bool
| .default, _ => true
| .range n, sc => sc.val.val / 100 = n
| .exact sc1, sc2 => sc1 = sc2

def Response.map (f : a -> b) (r : Response a) : Response b :=
  { r with body := f r.body }
