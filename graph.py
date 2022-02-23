from collections import *
from re import L, S
from typing import *
from queue import PriorityQueue
import random
import math

class Graph:
    def __init__(self, connections: List[Tuple[str, str, int]], directed: bool = False) -> None:
        self._graph: DefaultDict[str, Dict[str, int]] = defaultdict(lambda: defaultdict(int))
        self._vertices: Set[str] = set()
        self._directed = directed
        #to be used in finding bridges:
        self._counter: int = 0
        self._visited: set = set()
        self._lowlinked: DefaultDict[str, int] = defaultdict()
        self._id: DefaultDict[str,int] = defaultdict()
        self._bridges: set[tuple] = set()
        #^ used in finding bridges
        #to be use in finding strongly connected components
        self._stack: List[str] = []
        self._scccount: int = 0
        self._onstack: DefaultDict[str, bool] = defaultdict()
        #^ used in finding strongly connected components
        #to be used in finding eulerian paths
        self._edges_out: DefaultDict[str, int] = defaultdict(lambda: 0)            
        self._edges_in: DefaultDict[str, int] = defaultdict(lambda: 0)
        self._eulerianpath: Deque[str] = deque()
        #^ used in finding eulerian paths
        for c1, c2, weight in connections:
            self.add_edge(c1, c2, weight)
            self.add_vertice(c1)
            self.add_vertice(c2)

    def add_edge(self, start: str, end: str, weight: int) -> None:
        self._graph[start][end] = weight
        if not self._directed:
            self._graph[end][start] = weight

    def add_vertice(self, node: str) -> None:
        self._vertices.add(node)

    def get_edge_degree(self) -> None:
        self._edges_in.clear()
        self._edges_out.clear()
        for node in self._graph:
            for neighbour in self._graph[node]:
                self._edges_out[node] += 1
                self._edges_in[neighbour] += 1

    def __str__(self) -> str:
        return str(dict(self._graph))

    def bfs(self) -> Iterator[str]:
        aux: Deque[str] = deque()
        visited: Set[str] = set()
        for node in self._graph.keys():
            if node not in visited:
                visited.add(node)
                aux.append(node)
            while aux:
                curr = aux.popleft()
                yield curr
                # to avoid defaultdict automatically adding a default key
                # to self._graph
                if curr in self._graph:
                    for neighbour in self._graph[curr]:
                        if neighbour not in visited:
                            visited.add(neighbour)
                            aux.append(neighbour)

    def dfs_aux(self, start_node: str, visited: Deque[str]) -> Iterator[str]:
        if start_node not in visited:
            yield start_node
            visited.append(start_node)
            for neighbour in self._graph[start_node]:
                yield from self.dfs_aux(neighbour, visited)
    
    def dfs(self) -> Iterator[str]:
        visited: Deque(str) = deque()
        for node in list(self._graph.keys()):
            if node not in visited:
                for curr in self.dfs_aux(node, deque()):
                    visited.append(curr)
        for dfs_node in visited:
            yield dfs_node

    def top_aux(self, start_node: str, visited: Deque[str]) -> Iterator[str]:
        if start_node not in visited:
            visited.append(start_node)
            for neighbour in self._graph[start_node]:
                yield from self.top_aux(neighbour, visited)    
            yield start_node
    
    def top_sort(self) -> Deque[str]:
        visited: Deque[str] = deque()
        sorted_subgraph: Deque[str] = deque()
        sorted_graph: Deque[str] = deque()
        for node in list(self._graph.keys()):
            if node not in visited:
                for curr in self.top_aux(node, visited):
                    visited.append(curr)
                    sorted_subgraph.appendleft(curr)
                sorted_graph =  sorted_subgraph + sorted_graph
                sorted_subgraph = deque()
        return sorted_graph

    def sssp_dag(self, start_node: str, end_node: str) -> int:
        #single source shortest part on directed acyclic graph
        top_sorted: Deque[str] = self.top_sort()
        distances: DefaultDict[str, int] = defaultdict()
        distances[start_node] = 0
        for node in list(top_sorted):
            if node != start_node:
                top_sorted.popleft()
            elif node == start_node:
                break
        for node in list(top_sorted)[::-1]:
            if node != end_node:
                top_sorted.pop()
            elif node == end_node:
                break
        for node in top_sorted:
            if node != start_node:
                distances[node] = math.inf
        for node in list(top_sorted):
            for neighbour in self._graph[node]:
                if self._graph[node][neighbour] + distances[node] < distances[neighbour]:
                    distances[neighbour] = self._graph[node][neighbour] + distances[node]
        return distances[end_node]
    
    def dijkstras(self, start_node: str) -> Dict:
        #single source shortest path, for graph only containing non-negative edge weights
        #O((V + E)log(v))
        pqueue: PriorityQueue[int, str] = PriorityQueue()
        visited: set[str] = set()
        distances: DefaultDict[str, int] = defaultdict()
        distances[start_node] = 0
        for node in self._vertices:
            if node != start_node:
                distances[node] = math.inf
        visited.add(start_node)
        pqueue.put((0, start_node))
        while len(pqueue.queue) != 0:
            (dist,node) = pqueue.get()
            if node in self._graph:
                for neighbour in self._graph[node]:
                   if self._graph[node][neighbour] + dist < distances[neighbour]:
                       distances[neighbour] = self._graph[node][neighbour] + dist
                       pqueue.put((distances[neighbour], neighbour))
        return distances

    def bellman_ford(self, start_node: str) -> Dict:
        #single source shortest path, detecting negative cycles
        #O(VE)
        distances: DefaultDict[str, int] = defaultdict()
        distances[start_node] = 0
        for node in self._vertices:
            if node != start_node:
                distances[node] = math.inf
        #first iteration of algorithm (finding shortest distances assuming no negative cycles)
        for counter in range(len(distances)-1):
            for node in self._graph:
                for neighbour in self._graph[node]:
                    if self._graph[node][neighbour] + distances[node] < distances[neighbour]:
                        distances[neighbour] = self._graph[node][neighbour] + distances[node]
        #second iteration of algorithm (finding negative cycles)
        for counter in range(len(distances)-1):
            for node in self._graph:
                for neighbour in self._graph[node]:
                    if self._graph[node][neighbour] + distances[node] < distances[neighbour]:
                        distances[neighbour] = -math.inf
        return distances

    def dfs_bridges(self, start_node: str, parent: str) -> set[tuple]:
        if start_node not in self._visited:
            self._visited.add(start_node)
            self._counter = self._counter + 1
            self._lowlinked[start_node] = self._id[start_node] = self._counter
            for neighbour in self._graph[start_node]:
                if neighbour == parent:
                    continue
                if neighbour not in self._visited:
                    self.dfs_bridges(neighbour, start_node)
                    self._lowlinked[start_node] = min(self._lowlinked[start_node], self._lowlinked[neighbour])
                    if self._id[start_node] < self._lowlinked[neighbour]:
                        self._bridges.add((start_node, neighbour))
                else:
                    self._lowlinked[start_node] = min(self._lowlinked[start_node], self._id[neighbour])

    def find_bridges(self) -> set[tuple]:
        for node in self._vertices:
            self.dfs_bridges(node, '')
        self._counter: int = 0
        self._visited: set = set()
        self._lowlinked: DefaultDict[str, int] = defaultdict()
        self._id: DefaultDict[str,int] = defaultdict()
        return self._bridges

    def dfs_scc(self, start_node: str) -> None:
        #depth first search for Tarjan's algorithm of finding strongly connected components
        if start_node not in self._visited:
            self._visited.add(start_node)
            self._stack.append(start_node)
            self._onstack[start_node] = True
            self._counter = self._counter + 1
            self._lowlinked[start_node] = self._id[start_node] = self._counter
            for neighbour in self._graph[start_node]:
                if neighbour not in self._visited:
                    self.dfs_scc(neighbour)
                if self._onstack[neighbour]:
                    self._lowlinked[start_node] = min(self._lowlinked[start_node], self._lowlinked[neighbour])
            if self._id[start_node] == self._lowlinked[start_node]:
                checker: bool = True
                while checker:
                    node = self._stack.pop()
                    self._onstack[node] = False
                    self._lowlinked[node] = self._id[start_node]
                    if node == start_node:
                        checker = False
                self._scccount += 1

    def find_scc(self) -> int:
        for node in self._vertices:
            if node not in self._visited:
                self.dfs_scc(node)
        print(self._lowlinked)
        return self._scccount
    
    def dfs_eulerian(self, start_node) -> List:
        if self._edges_out[start_node] != 0:
            next_node = list(self._graph[start_node].keys())[self._edges_out[start_node]-1]
            self._edges_out[start_node] -= 1
            self.dfs_eulerian(next_node)
        self._eulerianpath.appendleft(start_node)
    
    def find_eulerian(self) -> Deque[str]:
        #does not allow for double edges
        self.get_edge_degree()
        start_nodes = end_nodes = 0
        starting_node = ending_node = list(self._vertices)[0]
        for node in self._vertices:
            if self._edges_out[node] - self._edges_in[node] > 1 or self._edges_in[node] - self._edges_out[node] > 1:
                start_nodes == 2
            elif self._edges_out[node] - self._edges_in[node] == 1:
                start_nodes += 1
                starting_node = node
            elif self._edges_in[node] - self._edges_out[node] == 1:
                end_nodes += 1
                ending_node  = node
        if (start_nodes == 0 and end_nodes == 0) or (start_nodes == 1 and end_nodes == 1):
            self.dfs_eulerian(starting_node)
            return self._eulerianpath
                
    def prim(self) -> List[str]:
        #minimum spanning tree for weighted undirected graph
        if not self._directed:
            visited: set[str] = set()
            edges: int = 0
            required: int = len(self._vertices) - 1
            pqueue: PriorityQueue[int, tuple] = PriorityQueue()
            node: str = list(self._vertices)[0]
            result: List[tuple] = []
            while edges != required:
                if node not in visited:
                    visited.add(node)
                    for neighbour in self._graph[node]:
                        pqueue.put((self._graph[node][neighbour], (node, neighbour)))
                (weight, (start_node, end_node)) = pqueue.get()
                if end_node not in visited:
                    result.append((start_node, end_node))
                    edges += 1
                    node = end_node
        return result
                        
                    
                



graph = Graph([
    ('A', 'B', 1),
    ('B', 'E', 1),
    ('B', 'D', 1),
    ('C', 'D', 1),
    ('D', 'B', 1),
    ('D', 'G', 1),
    ('C', 'F', 1),
    ('H', 'I', 1)
])

graph_2 = Graph([
    ('C', 'A', 1),
    ('C', 'B', 1),
    ('E', 'A', 1),
    ('E', 'D', 1),
    ('E', 'F', 1),
    ('A', 'D', 1),
    ('B', 'D', 1),
    ('D', 'G', 1),
    ('D', 'H', 1),
    ('F', 'K', 1),
    ('F', 'J', 1),
    ('K', 'J', 1),
    ('J', 'M', 1),
    ('J', 'L', 1),
    ('H', 'J', 1),
    ('H', 'I', 1),
    ('I', 'L', 1),
    ('G', 'I', 1),        
], True)

graph_3 = Graph([
    ('A', 'B', 3),
    ('A', 'C', 6),
    ('B', 'C', 4),
    ('B', 'D', 4),
    ('B', 'E', 11),
    ('C', 'D', 8),
    ('D', 'E', -4),
    ('D', 'F', 5),
    ('D', 'G', 2),
    ('C', 'G', 11),
    ('E', 'H', 9),
    ('F', 'H', 1),
    ('G', 'H', 2)
], True)

graph_4 = Graph([
    ('A', 'B', 4),
    ('A', 'C', 1),
    ('C', 'B', 2),
    ('B', 'D', 1),
    ('C', 'D', 5),
    ('D', 'E', 3),
], True)

graph_5 = Graph([
    ('A', 'B', 5),
    ('B', 'C', 20),
    ('C', 'D', 10),
    ('D', 'C', -15),
    ('C', 'E', 75),
    ('E', 'J', 100),
    ('B', 'F', 30),
    ('B', 'G', 60),
    ('F', 'G', 5),
    ('G', 'H', -50),
    ('H', 'I', -10),
    ('F', 'I', 50),
    ('F', 'E', 25),    
], True)

graph_6 = Graph([
    ('A', 'B', 1),
    ('B', 'C', 1),
    ('C', 'A', 1),
    ('B', 'D', 1),
    ('D', 'E', 1),
    ('B', 'F', 1),
    ('F', 'G', 1),
    ('G', 'H', 1),
    ('H', 'I', 1),
    ('I', 'F', 1)
])

graph_7 = Graph([
    ('A', 'B', 1),
    ('B', 'C', 1),
    ('C', 'A', 1),
    ('D', 'E', 1),
    ('E', 'F', 1),
    ('F', 'G', 1),
    ('F', 'A', 1),
    ('G', 'E', 1),
    ('G', 'A', 1),
    ('G', 'C', 1),
    ('D', 'H', 1),
    ('H', 'D', 1),
    ('H', 'F', 1)
], True)

graph_8 = Graph([
    ('A', 'B', 1),
    ('A', 'C', 1),
    ('C', 'A', 1),
    ('C', 'B', 1),
    ('B', 'D', 1),
    ('D', 'C', 1),
    ('D', 'F', 1),
    ('F', 'C', 1),
    ('C', 'E', 1),
    ('E', 'F', 1),
    ('F', 'A', 1)
],True)

graph_9 = Graph([
    ('A', 'B', 10),
    ('A', 'C', 1),
    ('A', 'D', 4),
    ('B', 'C', 3),
    ('C', 'D', 2),
    ('B', 'E', 0),
    ('C', 'F', 8),
    ('D', 'G', 7),
    ('D', 'F', 2),
    ('E', 'F', 1),
    ('F', 'G', 6),
    ('E', 'H', 8),
    ('F', 'H', 9),
    ('G', 'H', 12)
])

print(graph_9.prim())

# print(graph_7.find_scc())
# print(graph_8.find_eulerian())
# print(graph_4.dijkstras('A'))
# print(graph_5.bellman_ford('A'))
# for n in graph.bfs():
#    print(n)

# print(graph_6.find_bridges())

# print(graph_2.top_sort())
# print(graph_3.sssp_dag('A','H'))
# print(graph_3.top_sort())