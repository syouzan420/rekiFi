module Stages(stages,evts,players,initPos,gridSize,idef) where

import Define (Stage,Evt,Size,Pos,Def,Mode(..))

map0 :: Stage
map0 = [((0,2),('S',Bl)),((4,2),('M',Bl)),((2,4),('H',Bl))]

map1 :: Stage
map1 = [((2,0),('0',Bl))]

map2 :: Stage
map2 = []

map3 :: Stage
map3 = [((0,0),('z',Bl)),((1,0),('=',Bl)),((0,4),('a',Fr)),((2,4),('b',Fr)),((4,4),('c',Fr))]

map4 :: Stage
map4 = []

stages :: [Stage]
stages = [map0,map1,map2,map3,map4]

evts :: [Evt]
evts = []

players :: [Char]
players = "@@@@@"

initPos :: [Pos]
initPos = [(2,0),(2,2),(2,2),(2,2),(4,2)]

gridSize :: [Size]
gridSize = [(5,5),(5,5),(5,5),(5,5),(7,7)]

idef :: [(Def,Int)]
idef = []