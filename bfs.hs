type Graph = [[Int]]

bfs :: Graph -> Int -> [Int] -> Int
bfs _ _ [] = 0
bfs graph k q =
  let current = head q
      neighbors = graph !! current
      newQueue =
        tail q
          ++ filter (flip notElem q) neighbors
   in 1 + bfs graph k newQueue

-- Example graph: 0 -> 1 -> 2
--                 \-> 3
graph :: Graph
graph = [[1, 3], [2], [], []]

-- Start BFS from node 0
result :: Int
result = bfs graph 0 [0]

main :: IO ()
main = print result