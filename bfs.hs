-- Graph representation: adjacency list
type Graph = [(Int, [Int])]

-- BFS function
bfs :: Graph -> Int -> [Int]
bfs graph start = bfs' [start] []
  where
    bfs' [] visited = reverse visited
    bfs' (node : queue) visited
      | elem node visited = bfs' queue visited
      | otherwise = bfs' (queue ++ neighbors) (node : visited)
      where
        neighbors = maybe [] id (lookup node graph)

-- Example usage
main :: IO ()
main = do
  let graph = [(1, [2, 3]), (2, [4]), (3, [4]), (4, [])]
  print $ bfs graph 1