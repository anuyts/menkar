module Menkar.Syntax.Syntax where

import Menkar.Syntax.Algebra

data MenkarSyntax x v =
  Lam (x (Maybe v))
