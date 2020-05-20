{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

-- {-# OPTIONS_GHC -ddump-splices   #-}

#define CHECK(name, expr) \
name :: $(fmap quantifyType . typecheckExp =<< [e| expr |]); name = expr


module Typechecking where

import Language.Haskell.TH.Datatype
import AlgebraCheckers.Typechecking

CHECK(infixE, (5 `drop` []))
CHECK(infixE_l, (5 `drop`))
CHECK(infixE_r, (`drop` []))
CHECK(char, 'c')
CHECK(str, "str")
CHECK(sig, True :: Bool)
CHECK(app, drop 5)
CHECK(var, drop)
CHECK(con, True)
CHECK(parens, ((((True)))))
CHECK(list, ([True, False, True, False]))
CHECK(tup, (('c', "str", True)))
CHECK(lam, (\a b c -> not a && b || (c == "string")))

