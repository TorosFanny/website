---
title: Drawing graphs with gloss
date: 2013-05-27
published: false
---

Around a year ago, me and some friends wrote a [C++
tool](https://github.com/scvalex/visigoth) to generate and visualise
graphs.  I was surprised at how easy it is to "balance" graph vertices
so that they are laid out in a nice way.  This tutorial reproduces a
basic version of the algorithm in Haskell, using the
[`gloss`](http://hackage.haskell.org/package/gloss) library to get the
graph on the screen.  Apart from `gloss` nothing outside the Haskell
Platform is needed.

This tutorial is aimed at beginners, and only a basic knowledge of
Haskell is required---we disregard performance to have simple code, and
we don't make use of type classes.

Preliminaries
-------------

We import the libraries we need, qualifying `Map` and `Set` avoiding
clashes with the `Prelude`.

> import           Control.Monad (mplus)
> import           Data.Map.Strict (Map)
> import qualified Data.Map.Strict as Map
> import           Data.Set (Set)
> import qualified Data.Set as Set
> import           Graphics.Gloss
> import           Graphics.Gloss.Data.Vector
> import           Graphics.Gloss.Interface.Pure.Game
> import           Graphics.Gloss.Data.ViewState
> import           System.Random

The idea
--------

First, let's frame the problem we want to solve.  We have an undirected
graph, and we want to position its vertices on a surface so that the
result is pleasant to look at.  "Pleasant to look at" is still a very
vague requirement depending on fuzzy things like human taste, and in
fact there are [many ways to go at this
problem](http://www.graphviz.org/).

We will gain inspiration from physics, and take vertices to be like
charged particles repelling each other, and edges to be like "elastic
bands" pulling the vertices together.  We will calculate the forces and
update the positions in rounds, and hopefully after some time our graph
will stabilise.  With the right numbers, this gives surprisingly good
results.

The `Graph`
-----------

We need some kind of identifier for our vertices, we will simply go for
`Int`.  An `Edge` is a pair of `Vertex`s.

> type Vertex = Int
> type Edge = (Vertex, Vertex)

We want to store our graph so that the operations we need to execute are
as natural as possible.  Given the algorithm above, we need to do two
things well: iterating through all the vertices, and iterating through
the neighbours of a given vertex.  With that in mind, the obvious thing
to do is to have the graph to be a set of vertices, and a mapping from
each vertex to its neighbours.

> data Graph = Graph
>     { grVertices :: Set Vertex
>     , grNeighs   :: Map Vertex (Set Vertex)
>     }
>
> emptyGraph :: Graph
> emptyGraph = Graph{grVertices = Set.empty, grNeighs = Map.empty}

When we add a vertex, we add it to the set of vertices of the graph, and
make sure that a set of neighbours exist for that vertex.  In this way
adding existing vertices will not modify the graph.

> addVertex :: Vertex -> Graph -> Graph
> addVertex v gr@Graph{grVertices = vs, grNeighs = neighs} =
>     gr{ grVertices = Set.insert v vs
>       , grNeighs   = case Map.lookup v neighs of
>                          Nothing -> Map.insert v Set.empty neighs
>                          Just _  -> neighs
>       }

When we add an `Edge`, we first make sure that the vertices provided are
present in the graph by adding them, and then add each vertex to the
other vertex's neighbours.

> addEdge :: Edge -> Graph -> Graph
> addEdge (v1, v2) gr = gr'{grNeighs = neighs}
>   where
>     gr'    = addVertex v1 (addVertex v2 gr)
>     neighs = Map.insert v1 (Set.insert v2 (vertexNeighs v1 gr')) $
>              Map.insert v2 (Set.insert v1 (vertexNeighs v2 gr')) $
>              grNeighs gr'

For the purpose of this program we don't really need `addVertex` and
`addEdge` to be idempotent---we could assume vertices not to be present
when `addVertex` is used, and the `Edge`'s vertices to be present with
`addEdge`.  However making operations safe is always a good idea,
especially if the cost is very low like in this case.

`vertexNeighs` unsafely gets the neighbours of a given `Vertex`: the
precondition is that the `Vertex` provided is in the graph.

> vertexNeighs :: Vertex -> Graph -> Set Vertex
> vertexNeighs v Graph{grNeighs = neighs} = neighs Map.! v

This is all we need to implement the algorithm.  It is also useful to
have a function returing all the edges in the `Graph` so that we can
draw them.  `Set.foldr` and `Map.foldrWithKey` are equivalent to the
usual `foldr` for lists, with the twist that with a `Map` we fold over
the key and value at the same time.  Since the graph is undirected, we
"order" each edge so that the the vertex with the lower id appears
first: in this way we will avoid duplicates like `(1, 2)` and `(2, 1)`.

> graphEdges :: Graph -> Set Edge
> graphEdges = Map.foldrWithKey' foldNeighs Set.empty . grNeighs
>   where
>     -- For each vertex `v1', insert an edge for each neighbour `v2'.
>     foldNeighs v1 ns es =
>         Set.foldr' (\v2 -> Set.insert (order (v1, v2))) es ns
>     order (v1, v2) = if v1 > v2 then (v1, v2) else (v2, v1)


The `Scene`
-----------

Now that we have our graph, we need a data structure recording the
position of each point.  We also want to "grab" points to move them
around the area, so we add a field recording whether we have a `Vertex`
selected or not.  The invariant for `Scene` is that the set of `Vertex`s
in `scGraph` is the same as the set of keys in `scPoints`.

> data Scene = Scene
>     { scGraph     :: Graph
>     , scPoints    :: Map Vertex Point
>     , scSelected  :: Maybe Vertex
>     , scViewState :: ViewState
>     }
>
> emptyScene :: Scene
> emptyScene =
>     Scene{ scGraph     = emptyGraph
>          , scPoints    = Map.empty
>          , scSelected  = Nothing
>          , scViewState = viewStateInit }

Then two predictable operations: one that adds a `Vertex`, with its
initial position on the scene, and one that adds an `Edge`.  When adding
the `Edge`, we *need* both points to be already present---see the
invariant for `Scene`.

> scAddVertex :: Vertex -> Point -> Scene -> Scene
> scAddVertex v pt sc@Scene{scGraph = gr, scPoints = pts} =
>     sc{scGraph = addVertex v gr, scPoints = Map.insert v pt pts}
>
> scAddEdge :: Edge -> Scene -> Scene
> scAddEdge e@(v1, v2) sc@Scene{scGraph = gr, scPoints = pts} =
>     if Map.member v1 pts && Map.member v2 pts
>     then sc{scGraph = addEdge e gr}
>     else error "non existant point!"

It is also useful to have an helper to get the position of a `Vertex`.

> vertexPos :: Vertex -> Scene -> Point
> vertexPos v Scene{scPoints = pts} = pts Map.! v

Drawing
-------

Now we can write the functions to convert the `Scene` to a `Picture`.
Thanks to `gloss`, this is *extremely* easy: we are offered a simple
data type that `gloss` will use to get things on the screen.

Some constants:

> vertexRadius :: Float
> vertexRadius = 6
>
> vertexColor :: Color
> vertexColor = makeColor 1 0 0 1 -- Red
>
> edgeColor :: Color
> edgeColor = makeColor 1 1 1 0.8 -- Whiteish

Drawing a `Vertex` is simply drawing a circle.  We use `ThickCircle` to
get the circle to be filled instead of just an outline.

> drawVertex :: Vertex -> Scene -> Picture
> drawVertex v sc = Translate x y (ThickCircle (vertexRadius / 2) vertexRadius)
>   where (x, y) = vertexPos v sc

Drawing an `Edge` is drawing a `Line`.

> drawEdge :: Edge -> Scene -> Picture
> drawEdge (v1, v2) sc = Line [vertexPos v1 sc, vertexPos v2 sc]

Bringing everything together, we generate `Picture`s for all the
vertices and all the edges, and then combine those with the appropriate
colors.

> windowSize :: (Int, Int)
> windowSize = (640, 480)
>
> fromEdges :: StdGen -> [Edge] -> Scene
> fromEdges gen es =
>     foldr scAddEdge (fst (Set.foldr' addv (emptyScene, gen) vs)) es
>   where
>     vs = Set.fromList (concat [[v1, v2] | (v1, v2) <- es])
>
>     -- `fromIntegral' is needed to convert from `Int' to `Float'.
>     halfWidth  = fromIntegral (fst windowSize) / 2
>     halfHeight = fromIntegral (snd windowSize) / 2
>
>     addv v (sc, gen1) =
>         let (x, gen2) = randomR (-halfWidth,  halfWidth) gen1
>             (y, gen3) = randomR (-halfHeight, halfHeight) gen2
>         in  (scAddVertex v (x, y) sc, gen3)


> drawScene :: Scene -> Picture
> drawScene sc@Scene{scGraph = gr, scViewState = ViewState{viewStateViewPort = port}} =
>     applyViewPortToPicture port $
>     Pictures [Color vertexColor vertices, Color edgeColor edges]
>   where
>     vertices = Pictures [drawVertex n sc | n <- Set.toList (grVertices gr)]
>     edges    = Pictures [drawEdge e sc   | e <- Set.toList (graphEdges gr)]


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
>     if l > 0 -- If we are analysing the same vertex, l = 0
>     then (dx * weight / l, dy * weight / l)
>     else (0, 0)
>   where
>     weight   = adjust dt 120
>     (dx, dy) = local v1 v2
>     l        = 2 * (dx * dx + dy * dy)
>
> pullVelocity :: Int -> Float -> Point -> Point -> Vector
> pullVelocity nedges dt v1 v2 =
>     (-(dx / weight), -(dy / weight))
>   where
>     (dx, dy) = local v1 v2
>     weight   = adjust dt (fromIntegral (nedges + 1) * 10)
>
> updatePosition :: Float -> Vertex -> Scene -> Point
> updatePosition dt v1 sc@Scene{scPoints = pts, scGraph = gr} =
>     addVel v1pos (pull (push (0, 0)))
>   where
>     v1pos  = vertexPos v1 sc
>     neighs = vertexNeighs v1 gr
>
>     addVel (x, y) (x', y') = (x + x', y + y')
>
>     push vel =
>         Map.foldr' (\v2pos -> addVel (pushVelocity dt v1pos v2pos))
>                    vel pts
>     pull vel =
>         foldr (addVel . pullVelocity (Set.size neighs) dt v1pos)
>               vel [vertexPos v2 sc | v2 <- Set.toList neighs]

> updatePositions :: Float -> Scene -> Scene
> updatePositions dt sc@Scene{scSelected = sel, scGraph = gr} =
>     foldr uppt sc . Set.toList . grVertices $ gr
>   where
>     uppt n sc' =
>         let pt = if Just n == sel then vertexPos n sc
>                  else updatePosition dt n sc'
>         in scAddVertex n pt sc'
>
> inCircle :: Point -> Float -> Point -> Bool
> inCircle p sca center = magV (local center p) <= vertexRadius * sca
>
> findVertex :: Point -> Float -> Scene -> Maybe Vertex
> findVertex p1 sca Scene{scPoints = pts} =
>     Map.foldrWithKey'
>     (\v p2 m -> m `mplus` if inCircle p1 sca p2 then Just v else Nothing)
>     Nothing pts
>
> handleEvent :: Event -> Scene -> Scene
> handleEvent (EventKey (MouseButton MiddleButton) Down _ pos) sc =
>     case findVertex (invertViewPort port pos) (viewPortScale port) sc of
>         Nothing -> sc
>         Just v  -> sc{scSelected = Just v}
>  where viewState = scViewState sc
>        port      = viewStateViewPort viewState
> handleEvent (EventKey (MouseButton MiddleButton) Up _ _) sc =
>     sc{scSelected = Nothing}
> handleEvent (EventMotion pos) sc@Scene{scPoints = pts, scSelected = Just v} =
>     sc{scPoints = Map.insert v (invertViewPort port pos) pts}
>  where port = viewStateViewPort (scViewState sc)
> handleEvent ev sc = sc{scViewState = updateViewStateWithEvent ev (scViewState sc)}

> sampleGraph :: [Edge]
> sampleGraph =
>     [(1, 30), (1, 40), (8, 46), (8, 16), (10, 25), (10, 19), (10, 33),
>      (12, 8), (12, 36), (12, 17), (13, 38), (13, 24), (24, 49), (24, 13),
>      (24, 47), (24, 12), (25, 27), (25, 12), (27, 12), (27, 14), (29, 10),
>      (29, 8), (30, 24), (30, 44), (38, 29), (38, 35), (2, 42), (2, 35),
>      (2, 11), (14, 18), (14, 24), (14, 38), (18, 49), (18, 47), (26, 41),
>      (26, 42), (31, 39), (31, 47), (31, 25), (37, 26), (37, 16), (39, 50),
>      (39, 14), (39, 18), (39, 47), (41, 31), (41, 8), (42, 44), (42, 29),
>      (44, 37), (44, 32), (3, 20), (3, 28), (6, 45), (6, 28), (9, 6), (9, 16),
>      (15, 16), (15, 48), (16, 50), (16, 32), (16, 39), (20, 33), (33, 9),
>      (33, 46), (33, 48), (45, 15), (4, 17), (4, 15), (4, 12), (17, 21),
>      (19, 35), (19, 15), (19, 43), (21, 19), (21, 50), (23, 36), (34, 23),
>      (34, 24), (35, 34), (35, 16), (35, 18), (36, 46), (5, 7), (5, 36),
>      (7, 32), (7, 11), (7, 14), (11, 40), (11, 50), (22, 46), (28, 43),
>      (28, 8), (32, 28), (32, 39), (32, 42), (40, 22), (40, 47), (43, 11),
>      (43, 17)
>     ]
>
> sceneWindow :: Scene -> IO ()
> sceneWindow sc =
>     play (InWindow "Graph Drawing" (640, 480) (10, 10))
>          black 30 sc drawScene handleEvent updatePositions
>
> main :: IO ()
> main =
>     do gen <- getStdGen
>        sceneWindow (fromEdges gen sampleGraph)

Improvements
------------

*   **Performance**

    * FADE/Voronoi
    * Strictness
    * Arrays

*   **Code style**

    * Classes
    * Lens

*   **Functionality**

    * Adding vertices
    * Generating graphs
    * 3D view
