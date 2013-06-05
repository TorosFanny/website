---
title: Drawing graphs with gloss
date: 2013-05-27
published: false
---

> {-# LANGUAGE ViewPatterns #-}
> import Data.Map.Strict (Map)
> import Control.Monad (mplus)
> import Data.Set (Set)
> import Graphics.Gloss
> import Graphics.Gloss.Data.Vector
> import Graphics.Gloss.Interface.Pure.Game
> import qualified Data.Map.Strict as Map
> import qualified Data.Set as Set

> type Vertex = Int
> type Edge = (Vertex, Vertex)
>
> data Graph = Graph
>     { grVertices :: Set Vertex
>     , grNeighs   :: Map Vertex (Set Vertex)
>     }
>
> emptyGraph :: Graph
> emptyGraph = Graph {grVertices = Set.empty, grNeighs = Map.empty}
>
> addVertex :: Vertex -> Graph -> Graph
> addVertex n gr@Graph{grVertices = nodes, grNeighs = neighs} =
>     gr{ grVertices = Set.insert n nodes
>       , grNeighs   = maybe (Map.insert n Set.empty neighs) (const neighs)
>                               (Map.lookup n neighs) }
>
> vertexNeighs :: Vertex -> Graph -> Set Vertex
> vertexNeighs n Graph{grNeighs = neighs} = neighs Map.! n
>
> addEdge :: Edge -> Graph -> Graph
> addEdge (n1, n2) (addVertex n1 . addVertex n2 -> gr) = gr{grNeighs = neighs}
>   where
>     neighs = Map.insert n1 (Set.insert n2 (vertexNeighs n1 gr)) $
>              Map.insert n2 (Set.insert n1 (vertexNeighs n2 gr)) $
>              grNeighs gr
>
> graphEdges :: Graph -> Set Edge
> graphEdges = Map.foldrWithKey' foldNeighs Set.empty . grNeighs
>   where
>     foldNeighs n1 ns es =
>         Set.foldr' (\n2 -> Set.insert (order (n1, n2))) es ns
>     order (n1, n2) = if n1 > n2 then (n1, n2) else (n2, n1)
>
> data Scene = Scene
>     { scGraph    :: Graph
>     , scPoints   :: Map Vertex Point
>     , scSelected :: Maybe Vertex
>     }
>
> emptyScene :: Scene
> emptyScene =
>     Scene{ scGraph    = emptyGraph
>          , scPoints   = Map.empty
>          , scSelected = Nothing }
>
> scAddVertex :: Vertex -> Point -> Scene -> Scene
> scAddVertex n pt sc@Scene{scGraph = gr, scPoints = pts} =
>     sc{scGraph = addVertex n gr, scPoints = Map.insert n pt pts}
>
> scAddEdge :: Edge -> Scene -> Scene
> scAddEdge e@(n1, n2) sc@Scene{scGraph = gr, scPoints = pts} =
>     if Map.member n1 pts && Map.member n2 pts
>     then sc{scGraph = addEdge e gr}
>     else error "non existant point!"

> -- TODO use foldl'
> fromPoints :: ([(Vertex, Point)], [Edge]) -> Scene
> fromPoints (pts, es) =
>     foldr scAddEdge (foldr (uncurry scAddVertex) emptyScene pts) es
>
> getPos :: Vertex -> Scene -> Point
> getPos n Scene{scPoints = pts} = pts Map.! n

> vertexRadius :: Float
> vertexRadius = 3
>
> vertexColor :: Color
> vertexColor = makeColor 1 0 0 1
>
> edgeColor :: Color
> edgeColor = makeColor 1 1 1 0.8
>
> drawVertex :: Vertex -> Scene -> Picture
> drawVertex n sc = Translate x y (ThickCircle vertexRadius (vertexRadius * 2))
>   where (x, y) = getPos n sc
>
> drawEdge :: Edge -> Scene -> Picture
> drawEdge (n1, n2) sc = Line [getPos n1 sc, getPos n2 sc]
>
> drawScene :: Scene -> Picture
> drawScene sc@Scene{scGraph = gr} =
>     Pictures [Color vertexColor vertices, Color edgeColor edges]
>   where
>     vertices = Pictures [drawVertex n sc | n <- Set.toList (grVertices gr)]
>     edges    = Pictures [drawEdge e sc   | e <- Set.toList (graphEdges gr)]

> epsilon :: Float
> epsilon = 0.001
>
> fps :: Int
> fps = 30
>
> adjust :: Float -> Float -> Float
> adjust dt x = x * dt * fromIntegral fps
>
> local :: Point -> Point -> Vector
> local (x1, y1) (x2, y2) = (x1 - x2, y1 - y2)
>
> pushVelocity :: Float -> Point -> Point -> Vector
> pushVelocity dt v1 v2 =
>     if l > 0 -- If we are analysing the same node, l = 0
>     then (dx * weight / l, dy * weight / l)
>     else (0, 0)
>   where
>     weight   = adjust dt 150
>     (dx, dy) = local v1 v2
>     l        = 2 * (dx * dx + dy * dy)
>
> pullVelocity :: Int -> Float -> Point -> Point -> Vector
> pullVelocity nedges dt v1 v2 =
>     (-(dx / weight), -(dy / weight))
>   where
>     (dx, dy) = local v1 v2
>     weight = adjust dt (fromIntegral (nedges + 1) * 10)
>
> updatePosition :: Float -> Vertex -> Scene -> Point
> updatePosition dt v1 sc@Scene{scPoints = pts, scGraph = gr} =
>     let (xvel, yvel) = pull push in (v1x + xvel, v1y + yvel)
>   where
>     v1pos@(v1x, v1y) = getPos v1 sc
>     addVel (x, y) (x', y') = (x + x', y + y')
>     neighs = vertexNeighs v1 gr
>
>     push = Map.foldr' (\v2pos -> addVel (pushVelocity dt v1pos v2pos)) (0, 0) pts
>
>     -- TODO use foldl'
>     pull vel =
>         foldr (\v2pos -> addVel (pullVelocity (Set.size neighs) dt v1pos v2pos)) vel
>               [getPos v2 sc | v2 <- Set.toList (vertexNeighs v1 gr)]

> updatePositions :: Float -> Scene -> Scene
> updatePositions dt sc@Scene{scSelected = sel, scGraph = gr} =
>     foldr uppt sc . Set.toList . grVertices $ gr
>   where
>     uppt n sc' =
>         let pt = if Just n == sel then getPos n sc else updatePosition dt n sc'
>         in scAddVertex n pt sc'
>
> inCircle :: Point -> Point -> Bool
> inCircle p center = magV (local center p) <= vertexRadius
>
> findVertex :: Point -> Scene -> Maybe Vertex
> findVertex p1 (scPoints -> pts)=
>     Map.foldrWithKey'
>     (\v p2 m -> m `mplus` if inCircle p1 p2 then Just v else Nothing)
>     Nothing pts
>
> handleEvent :: Event -> Scene -> Scene
> handleEvent (EventKey (MouseButton LeftButton) Down _ pos) sc =
>     case findVertex pos sc of
>         Nothing -> sc
>         Just v  -> sc{scSelected = Just v}
> handleEvent (EventKey (MouseButton LeftButton) Up _ _) sc =
>     sc{scSelected = Nothing}
> handleEvent (EventMotion pos) sc@Scene{scPoints = pts, scSelected = Just v} =
>     sc{scPoints = Map.insert v pos pts}
> handleEvent _ sc = sc

> dummy :: Scene
> dummy = fromPoints ([(1, (10, 10)), (2, (0, 0)), (3, (50, 50)), (4, (-20, -30))],
>                     [(1, 2), (2, 3), (3, 4), (4, 1)])
>
> sceneWindow :: Scene -> IO ()
> sceneWindow sc =
>     play (InWindow "Graph Drawing" (640, 480) (10, 10))
>          black 30 sc drawScene handleEvent updatePositions
>
> main :: IO ()
> main = sceneWindow dummy
