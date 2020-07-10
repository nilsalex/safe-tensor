{-# LANGUAGE OverloadedStrings #-}

module Lib (mainFun) where

import Math.Tensor
import Math.Tensor.Basic

import qualified Data.Map.Strict as M
import Data.IORef

import Control.Monad.Except
import qualified Data.Text as T

import System.Console.Haskeline

defEta :: IORef (M.Map T.Text (T Rational)) -> String -> String -> IO (Maybe String)
defEta tensorsRef identifier indices =
    case runExcept $ someEta "Spacetime" 4 a b of
      Left err -> return $ Just err
      Right t  -> do
                   modifyIORef' tensorsRef $ M.insert (T.pack identifier) t
                   return Nothing
  where
    a = T.singleton (indices !! 2)
    b = T.singleton (indices !! 3)

getTensorStr :: IORef (M.Map T.Text (T Rational)) -> String -> IO String
getTensorStr tensorsRef identifier = do
    m <- readIORef tensorsRef
    case M.lookup (T.pack identifier) m of
      Nothing -> return $ "tensor " <> identifier <> " does not exist"
      Just t' -> return $ show t'

getTensorRank :: IORef (M.Map T.Text (T Rational)) -> String -> IO String
getTensorRank tensorsRef identifier = do
    m <- readIORef tensorsRef
    case M.lookup (T.pack identifier) m of
      Nothing -> return $ "tensor " <> identifier <> " does not exist"
      Just t' -> return $ show $ rankT t'

mainFun :: IO ()
mainFun = do
    tensorsRef <- newIORef M.empty
    runInputT defaultSettings $ mainLoop tensorsRef

mainLoop :: IORef (M.Map T.Text (T Rational)) -> InputT IO ()
mainLoop tensorsRef = do
    line <- getInputLine "η "
    case line of
      Just ('d' : 'e' : 'f' : ' ' : identifier : ' ' : '\\' : 'e' : 't' : 'a' : indices)
        -> do
              res <- lift $ defEta tensorsRef [identifier] indices
              case res of
                Nothing  -> mainLoop tensorsRef
                Just err -> outputStrLn err >> mainLoop tensorsRef
      Just ('p' : 'r' : 'i' : 'n' : 't' : ' ' : identifier : _)
        -> do
            str <- lift $ getTensorStr tensorsRef [identifier]
            outputStrLn str
            mainLoop tensorsRef
      Just ('p' : 'r' : 'i' : 'n' : 't' : 'R' : ' ' : identifier : _)
        -> do
            str <- lift $ getTensorRank tensorsRef [identifier]
            outputStrLn str
            mainLoop tensorsRef
      Just "q" -> return ()
      Just str
        -> do
            outputStrLn $ "unknown command: " ++ str
            mainLoop tensorsRef
      Nothing -> mainLoop tensorsRef
