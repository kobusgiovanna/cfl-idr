package main

import (
	"os"
	"strconv"
	"bufio"
	"strings"
	"sort"
	"fmt"
	"hash/fnv"
)

func getAlphaGrammar(labelsP []int, labelsB []int) MCFG {
	if curr_grammar == "parity" {
		alphaGrammar, _ := dyck_alpha_grammar_k_parity(labelsP, labelsB, 1)
		return alphaGrammar
	}
	if curr_grammar == "parity2" {
		alphaGrammar, _ := dyck_alpha_grammar_k_parity(labelsP, labelsB, 2)
		return alphaGrammar
	}
	if curr_grammar == "se" {
		alphaGrammar, _ := dyck_alpha_grammar_k_parity_se(labelsP, labelsB, 2)
		return alphaGrammar
	}
	if curr_grammar == "project" {
		alphaGrammar, _ := dyck_alpha_grammar_k_parity(labelsP, labelsB, 1)
		return alphaGrammar
	}
	if curr_grammar == "exclude" {
		alphaGrammar, _ := dyck_alpha_grammar_k_parity(labelsP, labelsB, 1)
		return alphaGrammar
	}
	if curr_grammar == "all" {
		alphaGrammar, _ := dyck_alpha_grammar_k_parity_se(labelsP, labelsB, 2)
		return alphaGrammar
	}
	alphaGrammar, _ := dyck_alpha_grammar(labelsP, labelsB)
	return alphaGrammar
}

func getBetaGrammar(labelsP []int, labelsB []int) MCFG {
	if curr_grammar == "parity" {
		betaGrammar, _ := dyck_beta_grammar_k_parity(labelsP, labelsB, 1)
		return betaGrammar
	}
	if curr_grammar == "parity2" {
		betaGrammar, _ := dyck_beta_grammar_k_parity(labelsP, labelsB, 2)
		return betaGrammar
	}
	if curr_grammar == "se" {
		betaGrammar, _ := dyck_beta_grammar_k_parity_se(labelsP, labelsB, 2)
		return betaGrammar
	}
	if curr_grammar == "project" {
		betaGrammar, _ := dyck_beta_grammar_k_parity(labelsP, labelsB, 1)
		return betaGrammar
	}
	if curr_grammar == "exclude" {
		betaGrammar, _ := dyck_beta_grammar_k_parity(labelsP, labelsB, 1)
		return betaGrammar
	}
	if curr_grammar == "all" {
		betaGrammar, _ := dyck_beta_grammar_k_parity_se(labelsP, labelsB, 2)
		return betaGrammar
	}
	betaGrammar, _ := dyck_beta_grammar(labelsP, labelsB)
	return betaGrammar
}

func getProjectGrammar(labelsP []int, labelsB []int) MCFG {
	projectGrammar, _ := dyck_project_grammar(labelsP, labelsB)
	return projectGrammar
}

func getExcludeGrammar(labelsP []int, labelsB []int, label int) MCFG {
	//fmt.Println("getting exclude grammar")
	projectGrammar, _ := dyck_alpha_grammar_k_parity_exclude(labelsP, labelsB, 2, label)
	return projectGrammar
}

func readPathsFromFile(fileName string) []path {
	file, _ := os.Open(fileName)
	scanner := bufio.NewScanner(file)
	paths := []path{}
	for scanner.Scan() {
		line := scanner.Text()
		nums := strings.Fields(line)
		if len(nums) < 2 {
			continue
		}
		fstNum, _ := strconv.Atoi(nums[0])
		sndNum, _ := strconv.Atoi(nums[1])
		path := makePath(Vertex(fstNum),Vertex(sndNum))
		paths = append(paths, path)
	}
	return paths

}

func writePathsToFile(fileName string, paths []path) {
	file, _ := os.Create(fileName)
	defer file.Close()
	for _, path := range paths {
		outputWord := strconv.Itoa(int(path.start)) + " " + strconv.Itoa(int(path.end))
		outputBytes := []byte(outputWord + "\n")
		file.Write(outputBytes)
	}
}

func findPMR(v Vertex, parent *map[Vertex]Vertex) Vertex {
	if v != (*parent)[v] {
		(*parent)[v] = findPMR((*parent)[v], parent)
	} 
	return (*parent)[v]
}

func joinPMR(v Vertex, u Vertex, parent *map[Vertex]Vertex, weight *map[Vertex]int) {
	v = findPMR(v, parent)
	u = findPMR(u, parent)
	if v == u {
		return
	}
	if (*weight)[v] < (*weight)[u] {
		v, u = u, v
	}
	(*weight)[v] += (*weight)[u]
	(*parent)[u] = v
}

func condensateFromUnderApprox(g *graph, underApprox []path) (*graph, map[Vertex]Vertex){
	parent := make(map[Vertex]Vertex)
	weight := make(map[Vertex]int)

	for v, _ := range g.vertices {
		parent[v] = v
		weight[v] = 1
	}

	underMap := make(map[Vertex]map[Vertex]bool)
	for _, pair := range underApprox {
		if _, ok := parent[pair.start]; !ok { continue }
		if _, ok := parent[pair.end]; !ok { continue }
		fv := findPMR(pair.start, &parent)
		lv := findPMR(pair.end, &parent)
		if fv == lv {
			continue
		}
		if _, ok := underMap[fv]; !ok {
			underMap[fv] = make(map[Vertex]bool)
		}
		if _, ok := underMap[lv]; !ok {
			underMap[lv] = make(map[Vertex]bool)
		}
		underMap[fv][lv] = true
		if underMap[fv][lv] && underMap[lv][fv] {
			joinPMR(fv, lv, &parent, &weight)
		}
	}

	condensedGraph := MakeGraph()
	exists := make(map[Edge]bool)

	for _, e := range g.GetEdges() {
		fV := findPMR(e.From, &parent)
		tV := findPMR(e.To, &parent)
		newEdge := Edge{
			From:  fV,
			To:    tV,
			Label: e.Label,
		}
		if len(e.Label)==0 || exists[newEdge] {
			continue
		}
		exists[newEdge] = true
		condensedGraph.AddEdge(newEdge.From, newEdge.To, newEdge.Label)
	}

	return condensedGraph, parent
}

func getGraphFromEdgeMap(edgeMap map[Edge]bool) (*graph) {
	newGraph := MakeGraph()
	for edge, _ := range edgeMap {
		newGraph.AddEdge(edge.From, edge.To, edge.Label)
	}
	return newGraph
}

func (g *graph) Hash() uint64 {
	edgeStringList := []string{}
	for _, edge := range g.edgeList {
		if len(edge.Label) == 0 {
			continue
		}
		key := fmt.Sprintf("%v->%v[%v]", int(edge.From), int(edge.To), edge.Label)
		edgeStringList = append(edgeStringList, key)
	}
	sort.Strings(edgeStringList)
	key := fmt.Sprintf("%v", edgeStringList)
	h := fnv.New64a()
	h.Write([]byte(key))
	return h.Sum64()
}

func hashGWithInt (g *graph, i int) uint64 {
	edgeStringList := []string{}
	for _, edge := range g.edgeList {
		if len(edge.Label) == 0 {
			continue
		}
		key := fmt.Sprintf("%v->%v[%v]", int(edge.From), int(edge.To), edge.Label)
		edgeStringList = append(edgeStringList, key)
	}
	key := fmt.Sprintf("(%v)", i)
	edgeStringList = append(edgeStringList, key)
	sort.Strings(edgeStringList)
	key = fmt.Sprintf("%v", edgeStringList)
	h := fnv.New64a()
	h.Write([]byte(key))
	return h.Sum64()
}


var alphaSeenMap = map[uint64]bool{}
var alphaDeriToEdgeMap = map[uint64]map[uint64][]Edge{}
var alphaDeriToDeriMap = map[uint64]map[[2]uint64]bool{}
var alphaPathsMap = map[uint64][]path{}

//remember to always update deritoEdge and deritoDeri
func getAlphaPaths(g *graph, labelsP []int, labelsB []int) []path {
	graphHash := g.Hash()
	if !alphaSeenMap[graphHash] {
		//fmt.Println("running alpha", labelsP, labelsB)
		alphaSeenMap[graphHash] = true
		alphaGrammar := getAlphaGrammar(labelsP, labelsB)
		alphaPaths, _ := AllPairsReachability(g, &alphaGrammar, false, [][]Vertex{}, labelsP, labelsB)
		filterUsedEdges(&alphaPaths)
		alphaDeriToEdgeMap[graphHash] = deriToEdge
		alphaDeriToDeriMap[graphHash] = deriToDeri
		alphaPathsMap[graphHash] = alphaPaths
	} else {
		deriToEdge = alphaDeriToEdgeMap[graphHash]
		deriToDeri = alphaDeriToDeriMap[graphHash]
	}
	return alphaPathsMap[graphHash]
}

var betaSeenMap = map[uint64]bool{}
var betaDeriToEdgeMap = map[uint64]map[uint64][]Edge{}
var betaDeriToDeriMap = map[uint64]map[[2]uint64]bool{}
var betaPathsMap = map[uint64][]path{}

func getBetaPaths(g *graph, labelsP []int, labelsB []int) []path {
	graphHash := g.Hash()
	if !betaSeenMap[graphHash] {
		betaSeenMap[graphHash] = true
		betaGrammar := getBetaGrammar(labelsP,labelsB)
		betaPaths, _ := AllPairsReachability(g, &betaGrammar, false, [][]Vertex{}, labelsP, labelsB)
		filterUsedEdges(&betaPaths)
		betaDeriToEdgeMap[graphHash] = deriToEdge
		betaDeriToDeriMap[graphHash] = deriToDeri
		betaPathsMap[graphHash] = betaPaths
	} else {
		deriToEdge = betaDeriToEdgeMap[graphHash]
		deriToDeri = betaDeriToDeriMap[graphHash]
	}
	return betaPathsMap[graphHash]
}

var projectSeenMap = map[uint64]bool{}
var projectDeriToEdgeMap = map[uint64]map[uint64][]Edge{}
var projectDeriToDeriMap = map[uint64]map[[2]uint64]bool{}
var projectPathsMap = map[uint64][]path{}

func getProjectPaths(g *graph, labelsP []int, labelsB []int) []path {
	graphHash := g.Hash()
	if !projectSeenMap[graphHash] {
		projectSeenMap[graphHash] = true
		projectGrammar := getProjectGrammar(labelsP,labelsB)
		projectPaths, _ := AllPairsReachability(g, &projectGrammar, false, [][]Vertex{}, labelsP, labelsB)
		filterUsedEdges(&projectPaths)
		projectDeriToEdgeMap[graphHash] = deriToEdge
		projectDeriToDeriMap[graphHash] = deriToDeri
		projectPathsMap[graphHash] = projectPaths
	} else {
		deriToEdge = projectDeriToEdgeMap[graphHash]
		deriToDeri = projectDeriToDeriMap[graphHash]
	}
	return projectPathsMap[graphHash]
}

var excludeSeenMap = map[uint64]bool{}
var excludeDeriToEdgeMap = map[uint64]map[uint64][]Edge{}
var excludeDeriToDeriMap = map[uint64]map[[2]uint64]bool{}
var excludePathsMap = map[uint64][]path{}

func getExcludePaths(g *graph, labelsP []int, labelsB []int, currLabel int) []path {
	graphHash := hashGWithInt(g, currLabel)
	if !excludeSeenMap[graphHash] {
		excludeSeenMap[graphHash] = true
		excludeGrammar := getExcludeGrammar(labelsP,labelsB,currLabel)
		excludePaths, _ := AllPairsReachability(g, &excludeGrammar, false, [][]Vertex{}, labelsP, labelsB)
		filterUsedEdges(&excludePaths)
		excludeDeriToEdgeMap[graphHash] = deriToEdge
		excludeDeriToDeriMap[graphHash] = deriToDeri
		excludePathsMap[graphHash] = excludePaths
	} else {
		deriToEdge = excludeDeriToEdgeMap[graphHash]
		deriToDeri = excludeDeriToDeriMap[graphHash]
	}
	return excludePathsMap[graphHash]
}

func clearMaps() {
	alphaSeenMap = map[uint64]bool{}
	alphaDeriToEdgeMap = map[uint64]map[uint64][]Edge{}
	alphaDeriToDeriMap = map[uint64]map[[2]uint64]bool{}
	alphaPathsMap = map[uint64][]path{}
	betaSeenMap = map[uint64]bool{}
	betaDeriToEdgeMap = map[uint64]map[uint64][]Edge{}
	betaDeriToDeriMap = map[uint64]map[[2]uint64]bool{}
	betaPathsMap = map[uint64][]path{}
	projectSeenMap = map[uint64]bool{}
	projectDeriToEdgeMap = map[uint64]map[uint64][]Edge{}
	projectDeriToDeriMap = map[uint64]map[[2]uint64]bool{}
	projectPathsMap = map[uint64][]path{}
	excludeSeenMap = map[uint64]bool{}
	excludeDeriToEdgeMap = map[uint64]map[uint64][]Edge{}
	excludeDeriToDeriMap = map[uint64]map[[2]uint64]bool{}
	excludePathsMap = map[uint64][]path{}
	deriToEdge = map[uint64][]Edge{}
	deriToDeri = map[[2]uint64]bool{}
}

