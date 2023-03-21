module BST where
import Data.Graph (reachable)
import Data.Maybe (fromMaybe)
import GHC.Parser.Lexer (activeContext)
import Data.Map.Internal.Debug (node)
import GHC.Iface.Ext.Types (HieAST(nodeSpan))
import GHC (TransForm(ThenForm))

data BST a = Empty | BST (BST a) a (BST a) deriving Show

class Set s a where
  empty :: s a
  insert :: a -> s a -> s a 
  member :: a -> s a -> Bool

instance (Ord a) => Set BST a where
  empty :: BST a
  empty = Empty

  insert :: a -> BST a -> BST a
  insert x t@(BST lt y rt) = fromMaybe t (mostEfficientInsert t y)

    where
    
    -- This implementation of insert does at most d + 1 comparisons (d: depth of tree)
    -- And never creates an unneseccarry copy of nodes when inserting an existing node
    mostEfficientInsert :: BST a -> a -> Maybe (BST a)
    mostEfficientInsert Empty cand = 
     if cand == x 
     then 
      Nothing 
     else 
      return $ BST Empty x Empty

    mostEfficientInsert (BST lt y rt) cand =
     if x < y 
     then 
      mostEfficientInsert lt cand >>= \t -> return $ BST t y rt
     else
      mostEfficientInsert rt y >>= \t -> return $ BST lt y t
    
    -- Leverage the maybe monad instance here
    -- We try to insert the value as the first action in a 'monadic bind'
    -- (Left side of (>>=))
    -- If the node exists then 'efficientInsert' evaluates to Nothing
    -- The maybe implementation of >>= is defined to evaluate to Nothing
    -- If the first action evaluates to Nothing; The second action
    -- evaluates if the first action evalutes to Just ...
    -- Thats great because the second action is what does the copying!
    -- So no copying happens if the node exists
    efficientInsert :: BST a -> Maybe (BST a)
    efficientInsert Empty = return $ BST Empty x Empty
    efficientInsert (BST lt y rt)
      | x < y = efficientInsert lt >>= \v -> return $ BST v y rt   -- leverage the monad instance of maybe here
                                                             -- We try to insert the value as the first action (Left side of (>>=)) 
                                                             -- If the node exists then insertVal with evaluate to Nothing
                                                             -- The maybe implementation of >>= will evaluate to Nothing if the first action
                                                             -- evaluates to Nothing. This is good because now were saying: 
                                                             -- "First try to insert but don't do any copying until its guaranteed that the node doesnt exist already!"
                                                             -- Thats what happens next in the (a -> m b) function we define here... we create a "Copy" (BST .. .. ..)
                                                             -- and inject it into a maybe
      | x > y = efficientInsert rt >>= \v ->  return $ BST lt y v

      | otherwise = Nothing

    -- Every recursive iteration of this method creates a new copy by default
    -- Contrast this with the maybe version above that has a sortve 'try/catch'
    inefficientInsert :: a -> BST a -> BST a
    inefficientInsert value Empty = BST Empty value Empty
    inefficientInsert value tree@(BST leftTree treeVal rightTree)
      | value < treeVal = BST (inefficientInsert value leftTree) treeVal rightTree
      | value > treeVal = BST leftTree treeVal (inefficientInsert value rightTree)
      | otherwise = tree 

  member :: a -> BST a -> Bool
  member x Empty = False
  member x t@(BST lt val rt) = go x val t
    where

      go searchVal candidate Empty = searchVal == candidate

      go searchVal candidate (BST leftTree value rightTree)

        | searchVal < value = go searchVal candidate leftTree -- V
                                                              -- d+1 Comparisons
        | otherwise = go searchVal value rightTree            -- ^ because only
                                                            -- one comparison
                                                            -- takes at each level
                                                            -- plus 1 once we reach-- the empty level

complete :: a -> Int -> BST a
complete x d | d <  0 = Empty
complete x d | d == 0 = BST Empty x Empty
complete x d = BST t x t
  where
    t = complete x (d - 1)

balanced :: (Enum a, Ord a) => a -> Int -> BST a
balanced _ 0 = Empty
balanced x m = 
  if r == 1 
  then BST t x t
  else BST t' x t
  where
    (q, r) = quotRem m 2
    t = balanced x q
    t' = balanced x (q-1)
