/-  Copyright (C) 2023 The Http library contributors.

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

import Lean.Data.Json

namespace LeanOpenAPI

inductive PrimitiveDataType
/-- Mathematical integer (unbounded). -/
| integer
/-- JSON number: base 10, arbitrary length mantissa with arbitrary exponent. -/
| number
/-- UTF-8 string. -/
| string
/-- Plain ol' boolean. -/
| boolean

namespace PrimitiveDataType

inductive Format : PrimitiveDataType → Type
| int32       : Format .integer
| int64       : Format .integer
| float       : Format .number
| double      : Format .number
| byte        : Format .string
| binary      : Format .string
| date        : Format .string
| «date-time» : Format .string
| password    : Format .string
| custom (t) (format : String) : Format t
