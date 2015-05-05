###############################################################################
#		 _  ___  ____           ____  _____    _    ____  __  __ _____        #
#		/ |/ _ \| ___| _   _   |  _ \| ____|  / \  |  _ \|  \/  | ____|       #
#		| | (_) |___ \| | | |  | |_) |  _|   / _ \ | | | | |\/| |  _|         #
#		| |\__, |___) | |_| |  |  _ <| |___ / ___ \| |_| | |  | | |___        #
#		|_|  /_/|____/ \__, |  |_| \_\_____/_/   \_\____/|_|  |_|_____|       #
#	               		|___/                                                 #
###############################################################################

					Alexa Van Hattum 	(avanhatt)
					Aisha Ferrazares 	(aisha)
					Anjali Pal 			(ajpal)

								May 4, 2015

###############################################################################
#                                   Intro                                     #
###############################################################################
For our 195y final project, we used alloy (and then alloy*) to model a graph 
library. We then used our library to verify the correctness of Kruskal's 
algorithm for finding minimum spanning trees of weights, undirected graphs. We 
also demonstrated the versatility of our library by giving an example short 
proof, that if a directed, complete graph has a circle, it must have a 3 cycle
(shout out to cs22 for the idea). 

###############################################################################
#                               Graph Library                                 #
###############################################################################
Our design for graphs is as follows: We have sigs for Vertex and Edge. Vertex 
stores a relation from Vertex->Graph called neighbors. Basically, it is a set 
of all vertices reachable from each vertex, and the graph that it's in. Edge 
stores two vertices (its endpoints), a weight (Int), the set of Graphs the Edge 
appears in, and a relation from Vertex-> Vertex that essentially relates the 
two endpoints of the edge. We made Graph an abstract sig, with two sigs 
extending it: UGraph and DGraph, which are directed and undirected graphs, 
respectively. All graphs have a set of edges and a set of vertices. In directed
graphs, we consider v1 to be the source of the edge and v2 to be the 
destination, whereas in undirected graphs, we don't distinguish between v1 and 
v2. Basically, the neighbors and rels relations are different depending on 
whether the graph is directed or undirected, which is why we have Graph as an 
abstract sig with two sigs extending it. 

Our design makes a couple of stipulations about all graphs: there are no self 
edges, there are no duplicate edges, and all edges are part of at least one 
graph. As part of our graph library, we also have many predicates, which check 
common graph properties. We included predicates for completeness, connectedness,
and acyclicity (for both directed and undirected). At first when we made these 
predicates, we had them operate on graphs, but we later changed it so that they 
take in a set of edges and vertices and check whether the property would hold 
if a graph were constructed with those edges and vertices. The reason for this 
was that in most graph algorithms, you are actually looking at subsets of edges, 
not fully formed graphs. Also, it is much easier to decompose a graph into its 
edges and vertices than it is to form a graph out of a set of edges and 
vertices, so having the predicates operate on edges and vertices made more 
sense. 

###############################################################################
#                             Kruskal's Algorithm                             #
###############################################################################
A common application of graph theory in computer science is finding minimum
spanning trees of directed, weighted graphs. That is, given a graph that may 
represent something like a network of roads, find the subset of edges such that
every vertex is still reachable, but with the minimum sum of weights. We modeled 
this in alloy* (to allow quantification over sets) using the Event design idiom. 
We were able to verify for graphs up to 5 vertices (10 edges) that Kruskal’s 
algorithm always finds a valid minimum spanning tree. In addition, we optimized 
our implementation to include the union-by-rank and path compression heuristics 
of union-find. 

###############################################################################
#                               Three Cycle Proof                             #
###############################################################################
For any complete, directed graph with a cycle, there is a cycle of length three. 
We showed this property to be consistent for small scope in Alloy. Basically, we
made a predicate to check whether there was a cycle of length three in a graph.
Then we made a predicate saying that a directed graph was complete, not acyclic, 
and did not have a three cycle. Running in alloy, we were unable to find an 
instance in the scopes we tried, showing the theory to be consistent for small 
graphs.

###############################################################################
#                                  The End                                    #
###############################################################################
Thank you for a wonderful semester, and hope y'all have a fantastic summer! 
