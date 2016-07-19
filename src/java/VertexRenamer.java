import java.util.*;

public class VertexRenamer {
    private TreeMap<Integer, Integer> nameList;
    private String name;
	
    VertexRenamer(ArrayList<Integer> L, String name) {
	nameList = new TreeMap<Integer, Integer> (); 
	for(int i = 0; i < L.size(); ++i) {
	    nameList.put(L.get(i), i);
	}
	this.name = name;
    }
	
    VertexRenamer(TreeMap<Integer, Integer> nameList, String name) {
	this.nameList = nameList;
    }
	
    int nameOf(int v) {return nameList.get(v);}
	
    public VertexRenamer inverseMap() {
	TreeMap<Integer, Integer> ans = new TreeMap<Integer, Integer> ();
	
	for(int k : nameList.keySet()) {
	    ans.put(nameList.get(k), k);
	}
	
	return new VertexRenamer(ans, name + "_inv"); 	
    }
    
    // Returns a new Vertex Renamer where each value is increased by x.
    public VertexRenamer addX(int x) {
	TreeMap<Integer, Integer> M = new TreeMap<Integer, Integer> ();
	for(int k : nameList.keySet()) M.put(k, nameList.get(k) + x);
	return new VertexRenamer(M, name + "_plus_" + x);
    } 
    
    
    public Boundary renamedBoundary(Boundary b) {
	ArrayList<Integer> topPath = new ArrayList<Integer> ();
	for(int i = 0; i < b.topPathLength() + 2; ++i) {topPath.add(nameOf(b.topPathVertex(i)));}
	
	ArrayList<Integer> bottomPath = new ArrayList<Integer> ();
	for(int i = 0; i < b.bottomPathLength() + 2; ++i) {bottomPath.add(nameOf(b.bottomPathVertex(i)));}
	
	return new Boundary(topPath, bottomPath, name + "_app_" + b.getName());
    }
    
    public TreeSet<Integer> renamedSet(Set<Integer> S) {
	TreeSet<Integer> ans = new TreeSet<Integer> ();
	for(int s : S) ans.add(nameOf(s));
	return ans;
    }
    
    // makes a new VertexRenamer that first applies this and then r to the output.
    public VertexRenamer compose(VertexRenamer r) {
	TreeMap<Integer, Integer> ans = new TreeMap<Integer, Integer> ();
	for(int v : nameList.keySet()) ans.put(v, r.nameOf(nameOf(v)));
	return new VertexRenamer(ans, r.getName() + "_after_" + name);
    }
    
    public String getName() { return name; }

    public String toString() {return nameList.toString();}
    
}
