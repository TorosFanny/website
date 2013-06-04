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
>     , graphNEdges   :: Int
>     }
>
> emptyGraph :: Graph
> emptyGraph =
>     Graph {graphVertices = Set.empty, graphNeighs = Map.empty, graphNEdges = 0}
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
> addEdge (n1, n2) (addVertex n1 . addVertex n2 -> gr@Graph{graphNEdges = nedges}) =
>    gr{ graphNeighs = neighs
>      , graphNEdges = nedges + if Set.member n2 n1neighs then 1 else 0 }
>   where
>     n1neighs = (vertexNeighs n1 gr)
>     neighs = Map.insert n1 (Set.insert n2 n1neighs) $
>              Map.insert n2 (Set.insert n1 (vertexNeighs n2 gr)) $
>              graphNeighs gr
>
> graphEdges :: Graph -> Set Edge
> graphEdges = Map.foldrWithKey' foldNeighs Set.empty . graphNeighs
>   where
>     foldNeighs n1 ns es =
>         Set.foldr' (\n2 -> Set.insert (order (n1, n2))) es ns
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

> -- TODO use foldl'
> fromPoints :: ([(Vertex, Point)], [Edge]) -> Scene
> fromPoints (pts, es) =
>     foldr addEdge' (foldr (uncurry addVertex') emptyScene pts) es
>
> getPos :: Vertex -> Scene -> Point
> getPos n Scene{scenePoints = pts} = pts Map.! n

> vertexRadius :: Float
> vertexRadius = 3
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

> epsilon :: Float
> epsilon = 0.001
>
> fps :: Int
> fps = 30
>
> pushVelocity :: Point -> Point -> Vector
> pushVelocity (v1x, v1y) (v2x, v2y) =
>     if l > 0 -- If we are analysing the same node, l = 0
>     then (dx * 150 / l, dy * 150 / l)
>     else (0, 0)
>   where
>     (dx, dy) = (v1x - v2x, v1y - v2y)
>     l        = 2 * (dx * dx + dy * dy)
>
> pullVelocity :: Int -> Point -> Point -> Vector
> pullVelocity nedges (v1x, v1y) (v2x, v2y)= (-(dx / weight), -(dy / weight))
>   where
>     (dx, dy) = (v1x - v2x, v1y - v2y)
>     weight = fromIntegral (nedges + 1) * 10
>
> updatePosition :: Vertex -> Scene -> (Bool, Point)
> updatePosition v1 sc@Scene{ sceneGraph  = gr@Graph{graphNEdges = nedges}
>                           , scenePoints = pts } =
>     let (xvel, yvel) = pull push
>     in if xvel < epsilon && yvel < epsilon
>        then (True,  (v1x, v1y))
>        else (False, (v1x + xvel, v1y + yvel))
>   where
>     v1pos@(v1x, v1y) = getPos v1 sc
>     addVel (x, y) (x', y') = (x + x', y + y')
>
>     push = Map.foldr' (\v2pos -> addVel (pushVelocity v1pos v2pos)) (0, 0) pts
>
>     -- TODO use foldl'
>     pull vel =
>         foldr (\v2pos -> addVel (pullVelocity nedges v1pos v2pos)) vel
>               [getPos v2 sc | v2 <- Set.toList (vertexNeighs v1 gr)]

> updatePositions :: Float -> (Bool, Scene) -> (Bool, Scene)
> updatePositions _ (True,  sc) = (True, sc)
> updatePositions _ (False, sc) =
>     go False sc (Set.toList (graphVertices (sceneGraph sc)))
>   where
>     go stable sc' []       = (stable, sc')
>     go stable sc' (n : ns) =
>         let (nstable, pt ) = updatePosition n sc'
>         in go (stable && nstable) (addVertex' n pt sc') ns

> dummy :: Scene
> dummy = fromPoints ([(1, (10, 10)), (2, (0, 0)), (3, (50, 50)), (4, (-20, -30))],
>                     [(1, 2), (2, 3), (3, 4), (4, 1)])
>
> sceneWindow :: Scene -> IO ()
> sceneWindow sc =
>     play (InWindow "Graph Drawing" (200, 200) (10, 10))
>          black 30 (False, sc) (drawScene . snd) (const id) updatePositions
>
> main :: IO ()
> main = sceneWindow dummy

