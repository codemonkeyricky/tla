import Data.Maybe (fromMaybe)

-- Graph representation: adjacency list
type Graph = [(Int, [Int])]

-- DFS function
dfs :: Graph -> Int -> [Int] -> [Int]
dfs graph u visited
  | elem u visited = visited
  | otherwise =
      foldr (dfs graph) (u : visited) neighbors
  where
    neighbors = fromMaybe [] (lookup u graph)

-- Example usage
main :: IO ()
main = do
  let graph = [(1, [2, 3]), (2, [4]), (3, [4]), (4, [])]
  print $ dfs graph 1 [] -- Start DFS from node