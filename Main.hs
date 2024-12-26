import Haste (setTimer,Interval(Once,Repeat))
import Haste.Events (onEvent,preventDefault,KeyEvent(..),KeyData(..),
                     MouseEvent(..),MouseData(..),TouchEvent(..),TouchData(..))
import Haste.DOM (document,elemById,fromElem)
import Data.IORef(newIORef,readIORef,writeIORef)
import CvLoop (inputLoop,mouseClick,timerEvent)
import Browser (getCanvasInfo,cvRatio,tcStart,tcEnd,touchIsTrue,setBmps)
import Initialize (initState)
main :: IO ()
main = do
  bmps <- setBmps
  Just ce <- elemById "canvas"
  Just bup <- elemById "up"
  Just bleft <- elemById "left"
  Just bok <- elemById "ok"
  Just bright <- elemById "right"
  Just bdown <- elemById "down"
  Just c <- fromElem ce
  ci <- getCanvasInfo c
  state <- newIORef initState 
  onEvent bok Click $ \_ -> do 
    readIORef state >>= inputLoop c ci bmps 32 >>= writeIORef state
  onEvent bup Click $ \_ -> do 
    readIORef state >>= inputLoop c ci bmps 107 >>= writeIORef state
  onEvent bleft Click $ \_ -> do 
    readIORef state >>= inputLoop c ci bmps 104 >>= writeIORef state
  onEvent bright Click $ \_ -> do 
    readIORef state >>= inputLoop c ci bmps 108 >>= writeIORef state
  onEvent bdown Click $ \_ -> do 
    readIORef state >>= inputLoop c ci bmps 106 >>= writeIORef state
  onEvent document KeyDown $ \(KeyData kc _ _ _ _) -> do
    preventDefault
    readIORef state >>= inputLoop c ci bmps kc >>= writeIORef state
  onEvent ce Click $ \(MouseData xy _ _) -> do
    readIORef state >>= mouseClick c ci bmps xy >>= writeIORef state
  onEvent ce TouchStart $ \(TouchData {}) -> do
    readIORef state >>= tcStart >>= writeIORef state
  onEvent ce TouchEnd $ \(TouchData {}) -> do
    readIORef state >>= touchIsTrue >>= writeIORef state
    setTimer (Once 100) $ readIORef state >>= tcEnd >>= writeIORef state
    return ()
  setTimer (Repeat 50) $
    readIORef state >>= timerEvent c ci bmps >>= writeIORef state
  return ()
