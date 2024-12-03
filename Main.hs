import Haste (setTimer,Interval(Once,Repeat))
import Haste.Events (onEvent,preventDefault,KeyEvent(..),KeyData(..),
                     MouseEvent(..),MouseData(..),TouchEvent(..),TouchData(..))
import Haste.DOM (document,elemById,fromElem)
import Data.IORef(newIORef,readIORef,writeIORef)
import CvLoop (inputLoop,mouseClick)
import OutToCanvas (putMessageG)
import Browser (getCanvasInfo,cvRatio,tcStart,tcEnd,touchIsTrue,setBmps)
import Initialize (initState)
main :: IO ()
main = do
  (_, wsts) <- setBmps
  Just ce <- elemById "canvas"
  Just c <- fromElem ce
  ci <- getCanvasInfo c
  state <- newIORef initState 
  onEvent document KeyDown $ \(KeyData kc _ _ _ _) -> do
    preventDefault
    readIORef state >>= inputLoop c wsts ci kc >>= writeIORef state
  onEvent ce Click $ \(MouseData (x,y) _ _) -> do
    readIORef state >>= mouseClick c wsts ci x y >>= writeIORef state
  onEvent ce TouchStart $ \(TouchData {}) -> do
    readIORef state >>= tcStart >>= writeIORef state
  onEvent ce TouchEnd $ \(TouchData {}) -> do
    readIORef state >>= touchIsTrue >>= writeIORef state
    setTimer (Once 100) $ readIORef state >>= tcEnd >>= writeIORef state
    return ()
  setTimer (Repeat 50) $
    readIORef state >>= putMessageG c ci >>= writeIORef state
  return ()
