import java.util.*;
import java.io.*;

public class BoundaryListReader {
	Scanner sc;
	
	BoundaryListReader(Scanner sc) {this.sc = sc;}
	public void close() {sc.close();}
	
	Pair<ArrayList<Boundary>, ArrayList<String> > readBoundaries() {
		ArrayList<Boundary> boundaries = new ArrayList<Boundary> ();
		ArrayList<String> boundaryName = new ArrayList<String> ();
		
		while(sc.hasNext()) {
			boundaryName.add(sc.next());
			int tpl = sc.nextInt();
			int bpl = sc.nextInt();
			ArrayList<Integer> topPath = new ArrayList<Integer> ();
			ArrayList<Integer> bottomPath = new ArrayList<Integer> ();
			while(tpl-->0) {topPath.add(sc.nextInt());}
			while(bpl-->0) {bottomPath.add(sc.nextInt());}
			boundaries.add(new Boundary(topPath, bottomPath));
		}
		
		return new Pair<ArrayList<Boundary>, ArrayList<String> > (boundaries, boundaryName);
	}
	
	
	public static void main(String[] args) throws Exception {
		
		BoundaryListReader R = new BoundaryListReader(new Scanner(new File("data/boundaries.txt")));
		
		Pair<ArrayList<Boundary>, ArrayList<String> > BL = R.readBoundaries();
		
		for(int i = 0; i < BL.first.size(); ++i) {
			System.out.println(BL.second.get(i) + "  :  " + BL.first.get(i));
		}
		
		R.close();
	}
}
