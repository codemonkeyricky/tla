type Graph = [[Int]]

-- adjacency list, current node, to_visit nodes -> minimum distance
bfs :: Graph -> Int -> [Int] -> Int
bfs _ _ [] = 0
bfs al u q =
  let current = head q
      v = al !! current
      newQueue =
        tail q
          ++ filter (flip notElem q) v
   in 1 + bfs al u newQueue

-- Example graph: 0 -> 1 -> 2
--                 \-> 3
graph :: Graph
graph = [[1, 3], [2], [], []]

-- Start BFS from node 0
result :: Int
result = bfs graph 0 [0]

main :: IO ()
main = print result