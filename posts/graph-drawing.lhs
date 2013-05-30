---
title: Drawing graphs with gloss
date: 2013-05-27
published: false
---

> {-# LANGUAGE ViewPatterns #-}
> import Data.Map.Strict (Map)
> import Data.Set (Set)
> import Graphics.Gloss
> import qualified Data.Map.Strict as Map
> import qualified Data.Set as Set

> type Vertex = Int
> type Edge = (Vertex, Vertex)
>
> data Graph = Graph
>     { graphVertices :: Set Vertex
>     , graphNeighs   :: Map Vertex (Set Vertex)
>     }
>
> emptyGraph :: Graph
> emptyGraph = Graph {graphVertices = Set.empty, graphNeighs = Map.empty}
>
> addVertex :: Vertex -> Graph -> Graph
> addVertex n gr@Graph{graphVertices = nodes, graphNeighs = neighs} =
>     gr{ graphVertices = Set.insert n nodes
>       , graphNeighs   = maybe (Map.insert n Set.empty neighs) (const neighs)
>                               (Map.lookup n neighs) }
>
> vertexNeighs :: Vertex -> Graph -> Set Vertex
> vertexNeighs n Graph{graphNeighs = neighs} = neighs Map.! n
>
> addEdge :: Edge -> Graph -> Graph
> addEdge (n1, n2) (addVertex n1 . addVertex n2 -> gr) = gr{graphNeighs = neighs}
>   where neighs = Map.insert n1 (vertexNeighs n2 gr)
>                             (Map.insert n2 (vertexNeighs n1 gr) (graphNeighs gr))
>
> fromEdges :: [Edge] -> Graph
> fromEdges []                = emptyGraph
> fromEdges (e@(n1, n2) : es) = addEdge e (addVertex n1 (addVertex n2 (fromEdges es)))
>
> graphEdges :: Graph -> Set Edge
> graphEdges = Map.foldrWithKey' foldNeighs Set.empty . graphNeighs
>   where
>     foldNeighs n1 ns es = Set.foldr' (\n2 -> Set.insert (order (n1, n2))) es ns
>     order (n1, n2) = if n1 > n2 then (n1, n2) else (n2, n1)
>
> data Scene = Scene
>     { sceneGraph  :: Graph
>     , scenePoints :: Map Vertex Point
>     }
>
> emptyScene :: Scene
> emptyScene = Scene{sceneGraph = emptyGraph, scenePoints = Map.empty}
>
> addVertex' :: Vertex -> Point -> Scene -> Scene
> addVertex' n pt Scene{sceneGraph = gr, scenePoints = pts} =
>     Scene{sceneGraph = addVertex n gr, scenePoints = Map.insert n pt pts}
>
> addEdge' :: Edge -> Scene -> Scene
> addEdge' e@(n1, n2) sc@Scene{sceneGraph = gr, scenePoints = pts} =
>     if Map.member n1 pts && Map.member n2 pts
>     then sc{sceneGraph = addEdge e gr}
>     else error "non existant point!"
>

> -- TODO use foldl'
> fromPoints :: ([(Vertex, Point)], [Edge]) -> Scene
> fromPoints (pts, es) = foldr addEdge' (foldr (uncurry addVertex') emptyScene pts) es
>
> getPos :: Vertex -> Scene -> Point
> getPos n Scene{scenePoints = pts} = pts Map.! n

> vertexRadius :: Float
> vertexRadius = 6
>
> vertexColor :: Color
> vertexColor = makeColor 1 0 0 1
>
> edgeColor :: Color
> edgeColor = makeColor 1 1 1 0.5
>
> drawVertex :: Vertex -> Scene -> Picture
> drawVertex n sc = Translate x y (ThickCircle vertexRadius (vertexRadius * 2))
>   where (x, y) = getPos n sc
>
> drawEdge :: Edge -> Scene -> Picture
> drawEdge (n1, n2) sc = Line [getPos n1 sc, getPos n2 sc]
>
> drawScene :: Scene -> Picture
> drawScene sc@Scene{sceneGraph = gr} =
>     Pictures [Color vertexColor vertices, Color edgeColor edges]
>   where
>     vertices = Pictures [drawVertex n sc | n <- Set.toList (graphVertices gr)]
>     edges    = Pictures [drawEdge e sc   | e <- Set.toList (graphEdges gr)   ]

> dummy :: Scene
> dummy = fromPoints ([(1, (10, 10)), (2, (0, 0)), (3, (50, 50)), (4, (-20, -30))],
>                     [(1, 2), (2, 3), (3, 4), (4, 1)])

> sceneWindow :: Scene -> IO ()
> sceneWindow sc =
>     display (InWindow "Graph Drawing" (200, 200) (10, 10)) black (drawScene sc)

> updatePosition :: Vertex -> Scene -> (Bool, Point)
> updatePosition v1 sc@Scene{sceneGraph = gr, scenePoints = pts} = undefined
>   where
>     (v1x, v1y) = getPos v1 sc
>
>     repulsive = Map.foldr' repVel (0, 0) pts
>     repVel (v2x, v2y) (xvel, yvel) =
>         let (dx, dy) = (v1x - v2x, v1y - v2y)
>             l        = 2 * (dx * dx + dy * dy)
>         in if l > 0 -- If we are analysing the same node
>            then (xvel + (dx * 150) / l, yvel + (dy * 150) / l)
>            else (xvel, yvel)
>
>     -- TODO use foldl'
>     attractive vel =
>         foldr attVel vel [getPos v2 sc | v2 <- Set.toList (vertexNeighs v1 gr)]
>     attVel (v2x, v2y) (xvel, yvel) = undefined

> updatePositions :: Float -> (Bool, Scene) -> (Bool, Scene)
> updatePositions _ (True,  sc) = (True, sc)
> updatePositions _ (False, sc) =
>     go False sc (Set.toList (graphVertices (sceneGraph sc)))
>   where
>     go stable sc' []       = (stable, sc')
>     go stable sc' (n : ns) =
>         let (nstable, pt ) = updatePosition n sc'
>         in go (stable && nstable) (addVertex' n pt sc') ns

> main :: IO ()
> main = undefined
