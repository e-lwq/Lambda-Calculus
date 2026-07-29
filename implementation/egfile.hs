module Egfile where

import Basic
import Typed

x = PVar "x"
y = PVar "y"

ca = [("x",To (V 1) (V 2)), ("y", V 1)]
a = PApp (PApp x x) y

cb = [("x", To (V 1) (To (V 1) (V 2))), ("y", V 1)]
b = PApp (PApp x y) y

cc = [("x", To (V 1) (V 2)), ("y", To (To (V 1) (V 2)) (V 1))]
c = PApp (PApp x y) x

cd = [("x",To (V 1) (V 1)), ("y", V 1)]
d = PApp x (PApp x y)

ce = [("x",To (V 1) (V 2)), ("y",To (To (V 1) (V 2)) (V 1))]
e = PApp x (PApp y x)



