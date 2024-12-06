{-# LANGUAGE OverloadedStrings #-}
module CvLoop (inputLoop,mouseClick,timerEvent) where

import Haste.Graphics.Canvas(Canvas,Bitmap)
import Haste.Audio
import Control.Monad(unless)
import Data.List(intercalate,sort)
import Data.Maybe(fromMaybe)
import Text.Read(readMaybe)
import Data.Text(unpack)
import Define(State(..),Play(..),Switch(..),Mode(..),LSA(..),CInfo,Msg,miy,wg,wt)
import Stages(stages,players,initPos,gridSize)
import Grid(checkGrid,makeGrid)
import Browser(chColors,clFields,flToKc,fields,cvRatio,localStore,stringToJson)
import OutToCanvas(putMessageG,putMessageT,putGrid,putMoziCl,clearMessage
                  ,putPlayer,putMozi,putWst,putChara)
import Check(checkEv,getMessage)
import Libs(getRandomNumIO,sepByChar)
import Action(keyCodeToChar,keyChoice,keyCheck,putOut,plMove,makeChoiceMessage)
import Event(makeEvent)
import EReki (Rdt(..), reki)

type Bmps = ([Bitmap],[Bitmap],[Bitmap])

timerEvent :: Canvas -> CInfo -> Bmps -> State -> IO State
timerEvent c ci bmps st = do
  --次の課題
  --描画をアップデートする函數を別に設けて インプット時も利用できるやうにする
  let ticSt = tic st
      t = if ticSt > 254 then 0 else ticSt+1
      (szX,_) = sz st
      ((cvW,cvH),_) = ci
      (_,chrs,_) = bmps
      (chNum,anNum) = chr st
      gix = floor (cvW/wg) - 2
      p = player st
      grid = gr p 
      (px,py) = xy p
      anNum'
        | t `mod` 8 /= 0 = anNum
        | even anNum = anNum + 1
        | otherwise = anNum - 1
      chrIndex = chNum*8+anNum'
      nst = st{tic=t,chr=(chNum,anNum')}
  putGrid c (gix-szX,miy) grid 
  putPlayer c (px+gix-szX+1,py+miy+1) p
  --putMessageT c cvH
  putChara c chrs cvW szX chrIndex 
  putMessageG c ci nst

mouseClick :: Canvas -> CInfo -> Bmps -> (Int,Int) -> State -> IO State
mouseClick c ci bmps (x,y) = do
  let (rtx,rty) = cvRatio ci
      nx = fromIntegral x*rtx
      ny = fromIntegral y*rty
      cvWH = fst ci
  inputLoop c ci bmps (flToKc (clFields nx ny (fields cvWH))) 

skipMessage :: Canvas -> CInfo -> State -> IO State
skipMessage c ci st = do
  st' <- putMessageG c ci st
  let sw' = swc st'
  if imp sw' || not (ims (swc st)) then return st'{swc=sw'{ini=False}}
                                   else skipMessage c ci st'

choiceAction :: Canvas -> Double -> Int -> Int -> Char -> State -> IO State
choiceAction c cvH mix gix ch st = do
  print "choice"
  let hi = if ism (swc st) then snd (sz st) + 3 else 0
      (dlgs,mnas) = unzip (chd st)
      cn = chn st
      ncn = keyChoice (length dlgs - 1) cn ch 
  case ncn of
     (-1) -> do 
               let nmsg = getMessage [] (mnas!!cn)
               clearMessage c gix st
               return st{msg=nmsg,swc=(swc st){ims=True,ich=False,imp=False}}
     (-2) -> return st
     _    -> do
               let cmsg = makeChoiceMessage (msg st) dlgs ncn 
               clearMessage c gix st
               putMessageT c cvH (mix+ msc st,miy+hi) cmsg
               return st{chn=ncn}

rekiAction :: State -> IO State
rekiAction st = do
  let pl = player st 
      rekSt = rek st 
      stageNum = sn  pl
      randomG = rgn pl
  case rekSt of
    [n,l,r,jp] -> do
       let qt = fromMaybe 1 (readMaybe n) -- question type (1 or 2)
           qLng = length r -- number of questions
       (mondai,jun,ng) <- reki qt qLng randomG
       let ndef = [((l,333),stageNum),((makeRekiAns r jun,333),stageNum)]
           nmsg = makeRekiMon (zip mondai r)
           st' = st{player=pl{edf=edf pl++ndef,rgn=ng}, ems=ems st++nmsg, rek=[]}
           codeJp = ("e.==.m1:" ++ jp) : makeRekiJp r
           nst = foldl (flip makeEvent) st' codeJp
       return nst
    _ -> return st{rek=[]}

makeRekiJp :: String -> [String]
makeRekiJp = map (\ch ->"e.e" ++ [ch] ++ ".m0:" ++ [ch] ++ "Rk") 

makeRekiMon :: [(Rdt,Char)] -> [(String,Msg)]  
makeRekiMon = map (\(Rdt _ mon _ _,ch)-> (ch:"Rk",mon))

makeRekiAns :: String -> [Int] -> String
makeRekiAns str = map (\i -> fromMaybe ' ' (lookup i (zip [1..] str)))

mapAction :: Canvas -> CInfo -> Bmps -> Int -> Char -> State -> IO State
mapAction c ci bmps gix ch st = do
  let irkSt = not $ null $ rek st
  rst <- if irkSt then rekiAction st else return st
  let p@(Play xyP _ _ _ _ _ rgnP elgP _ iscP) = player rst
  sequence_ [print (evt st),print (ecs st), print (mem st),print elgP,print iscP,print (jps st)]
  (_,nrg) <- getRandomNumIO (5,rgnP)
  let (x,y) = xyP 
      (wd,hi) = sz st
      gsx = gix-wd
      (x',y') = keyCheck (wd,hi) (x,y) ch 
      p' = plMove (x',y') p
      (tx,ty) = xy p'
      (px,py) = (x+1,y+miy+1)
      (px',py') = (tx+1,ty+miy+1)
      p'' = if ch==' ' then putOut p' else p'
      nst = checkEv 0 (elg p'') (evt rst) rst{player=p''{rgn=nrg}}
      nsw = swc nst
      (wd',_) = sz nst
      gsx' = gix-wd'
  putGrid c (gsx',miy) (gr (player nst))
  --unless (ims nsw) $ putMessageT c cvH (mix+msc nst,miy+hi+3) (msg nst)
  sData <- case ch of
             's' -> localStore Save "savedata" (makeSaveData st) 
             'r' -> localStore Load "savedata" ""
             'd' -> localStore Remv "savedata" ""
             _   -> return "---"
  if ch=='r' && sData/="loadError" then loadState c ci sData nst else do 
    print sData
    if ils nsw || ch=='n' then nextStage c ci bmps nst{swc=nsw{ims=False}} 
                         else do
          let pxy = (px'+gsx,py')
          if et (player nst)==' ' then putMozi c (chColors!!1) pxy [pl p'']
                                  else putMozi c (chColors!!2) pxy [pl p'']
          -- putWst c wsts 20 (23,3) 'あ' -- for wst drawing test
          return nst

inputLoop :: Canvas -> CInfo -> Bmps -> Int -> State -> IO State 
inputLoop c ci@((cvW,cvH),_) bmps kc st
  | iniSt = return st
  | imsSt && not impSt = skipMessage c ci st{swc=sw{ini=True}} 
  | impSt = if ichSt then choiceAction c cvH mix gix ch st else return st{swc=sw{imp=False}}
  | ismSt = mapAction c ci bmps gix ch st
  | otherwise = return st 
       where sw = swc st
             iniSt = ini sw; impSt = imp sw; imsSt = ims sw
             ichSt = ich sw; ismSt = ism sw
             mix = floor (cvW/wt) - 1; gix = floor (cvW/wg) - 2
             ch = keyCodeToChar kc

makeSaveData :: State -> String
makeSaveData st =
  let stageData = sn$player st
      evtData = intercalate "," $ concatMap (\(tr,tg) -> [tr,tg]) (evt st)
      ecsData = intercalate "," $ map show (ecs st)
   in "\""++intercalate "~" [show stageData,evtData,ecsData]++"\""

loadState :: Canvas -> CInfo -> String -> State -> IO State
loadState _ _ "" st = return st
loadState c ci str st = do
  let dt = if head str=='\"' then tail$init str else str
      dts = sepByChar '~' dt
      nsn = read (head dts)
      evtStr = dts!!1
      nevt = listToTupples (sepByChar ',' evtStr)
      ecsStr = dts!!2
      necs = map read $ sepByChar ',' ecsStr
      nsz = gridSize!!nsn
      npl = players!!nsn
      nxy = initPos!!nsn
      ngr = makeGrid nsz (stages!!nsn)
      nst = st{player=(player st){xy=nxy, gr=ngr, pl=npl, et=' ', sn=nsn},sz=nsz,evt=nevt,ecs=necs}
  return nst

listToTupples :: [String] -> [(String,String)]
listToTupples [] = []
listToTupples [x] = []
listToTupples (x:y:xs) = (x,y):listToTupples xs

nextStage :: Canvas -> CInfo -> Bmps -> State -> IO State 
nextStage c ci bmps st = do
  let p = player st
      js = jps st
      nsn = if js<0 then sn p + 1 else js
      maxSn = length stages
      gc = nsn == maxSn
      nlg = elg p++'c':show (sn p)
  if gc then gameClear c st
        else do
          let nsz=gridSize!!nsn
              grid=makeGrid nsz (stages!!nsn)
              iwn=checkGrid (' ',Wn) grid
              np = p{xy=initPos!!nsn, gr=grid, pl=players!!nsn, et=' ',sn=nsn,
                     elg=nlg,isc=False,iw=iwn}
          inputLoop c ci bmps 64 st{sz=nsz,player=np,msg="",jps = -1,swc=(swc st){ils=False,igc=False}}

gameClear :: Canvas -> State -> IO State 
gameClear c st = do putMoziCl c
                    let col=head chColors
                    putMozi c col (2,5) "Congratulations!"
                    putMozi c col (3,8) "Coding : yokoP"
                    putMozi c col (3,10) "Test Play : takaPon"
                    putMozi c col (2,17) "Thank you for playing!"
                    let nsz=head gridSize
                        p = player st
                        np=p{xy = head initPos, gr=makeGrid nsz (head stages),
                             pl=head players,et=' ',sn=0,elg="",isc=False}
                    return st{sz=nsz,player=np,swc=(swc st){igc=False}}

