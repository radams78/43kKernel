import java.io.File;
import java.util.*;

/**
 * Set of boundaries + pre-computed values. The boundary set needs to be "gluing-closed" 
 * i.e; whenever a and b are in the garden and a glues onto b then a+b must also be
 * in the garden.
 */
public class BoundaryGarden {
    
    /** number of boundarues */
    public final int n;
    
    // List of canonized boundaries
    private ArrayList<Boundary> boundaries;

    // List of boundary names
    private ArrayList<String> boundaryNames;

    // List of everyone each boundary can glue on to
    private ArrayList<ArrayList<Integer> > gluesOnto;

    // 2D array, for each i,j that can be glued contains the signature gluing operator
    private ArrayList<ArrayList<SignatureComputer> > sigCom;

    // 2D array of gluing result for each pair that can be glued
    // -1 of it can't be
    private ArrayList<ArrayList<Integer> > gluingResult;

    private String name;

    /**
     * Given a list of boundaries and a list of names,
     * populates the boundary garden, then calculates;
     * <ul>
     * <li>for each pair of boundaries, whether they can glue together using {@link Boundary#canGlue}
     * <li>calculates the result of gluing them together - crashes if this is not in garden
     * <li>calculates the list of valid inputs for each boundary
     * <li>creates a {@link SignatureComputer} for each pair
     * </ul>
     *
     * @param boundaryList     list of boundaries
     * @param boundaryNameList list of names in same order
     */
    public BoundaryGarden (ArrayList<Boundary> boundaryList, ArrayList<String> boundaryNameList, String name) {
	boundaries = new ArrayList<Boundary> ();
	for(Boundary b : boundaryList) {boundaries.add(b.canonicalBoundary());}
	n = boundaries.size();
	
	boundaryNames = boundaryNameList;
	
	setGluesOnto();
	setGluingResult();
	setInputList();
	
	// has to be done last
	setSigCom();

	this.name = name;
    }
    
    public Boundary getBoundary(int p) {return boundaries.get(p);}
    public int boundaryId(Boundary b) {return boundaries.indexOf(b);}
    
    public String getBoundaryName(int p) {return boundaryNames.get(p);}
    public int getIdOfBoundaryWithName(String s) {return boundaryNames.indexOf(s);}
	
    public ArrayList<Integer> getGluesOnto(int p) {return gluesOnto.get(p);}
    public int getGluingResult(int i, int j) {return gluingResult.get(i).get(j);}
    public boolean canGlue(int i, int j) {return gluingResult.get(i).get(j) != -1;}
	
    public SignatureComputer getSignatureComputer(int i, int j) {return sigCom.get(i).get(j);}
	
    /** List of inputs for every boundary */
    private ArrayList<ArrayList<InputPair> > inputList;
    public ArrayList<InputPair> getAllInputs(int p) {return inputList.get(p);}
	
    private void setGluesOnto() {
	gluesOnto = new ArrayList<ArrayList<Integer> > ();
	for(int i = 0; i < n; ++i) {
	    gluesOnto.add(new ArrayList<Integer> ());
	    for(int j = 0; j < n; ++j) {
		if(getBoundary(i).canGlue(getBoundary(j))) gluesOnto.get(i).add(j); 
	    }
	}
    }
    
    private void setGluingResult() {
	gluingResult = new ArrayList<ArrayList<Integer> > ();
	for(int i = 0; i < n; ++i) {
	    gluingResult.add(new ArrayList<Integer> ());
	    for(int j = 0; j < n; ++j) {
		if(!gluesOnto.get(i).contains(j)) {
		    gluingResult.get(i).add(-1);
		} else {
		    Boundary glueResult = getBoundary(i).glue(getBoundary(j));
		    int resultID = boundaryId(glueResult);
		    assert resultID >= 0 : "Can glue " + getBoundaryName(i) + " onto " + getBoundaryName(j) 
			+ ", but result is not in garden.";
		    gluingResult.get(i).add(resultID);
		}
	    }
	}
    }
    
    private void setInputList() {
	inputList = new ArrayList<ArrayList<InputPair> > ();
	for(int i = 0; i < n; ++i) {inputList.add(getBoundary(i).allValidInputs());}
    }
    
    private void setSigCom() {
	sigCom = new ArrayList<ArrayList<SignatureComputer> > ();
	for(int i = 0; i < n; ++i) {
	    sigCom.add(new ArrayList<SignatureComputer> ());
	    for(int j = 0; j < n; ++j) {
		if(canGlue(i,j)) {
		    sigCom.get(i).add(new SignatureComputer(this, i, j, name + "_" + i + "_" + j));					
		} else {
		    sigCom.get(i).add(null);
		}
	    }
	}
    }
    
    // TESTING
    public static void main(String[] args) throws Exception {
	
	System.out.print("Reading input ...");
	BoundaryListReader BLR = new BoundaryListReader(new Scanner(new File("boundaries.txt")));
	Pair<ArrayList<Boundary>, ArrayList<String> > BL = BLR.readBoundaries();
	BLR.close();
	System.out.println("done.");
	
	System.out.print("Populating Boundary Garden ... ");
	BoundaryGarden myGarden = new BoundaryGarden(BL.first, BL.second, "boundary_garden");
	System.out.println("done.");
	
	myGarden.printGardenStats();
    }
    
    public static String normalizeLength(String s, int l) {
	String ans = new String(s);
	while(ans.length() < l) {ans = ans + " ";}
	return ans;
    }
    
    public void printGardenStats() {
	System.out.println("GLUES ONTO");
	for(int i = 0; i < n; ++i) {
	    System.out.print(normalizeLength(getBoundaryName(i), 5) + " : ");
	    for(int v : getGluesOnto(i)) System.out.print(normalizeLength(getBoundaryName(v),5) + " ");
	    System.out.println("");
	}
	
	System.out.println();
	System.out.println("GLUING RESULT");
	System.out.print("     " + " | ");
	for(int i = 0; i < n; ++i) {
	    System.out.print(normalizeLength(getBoundaryName(i), 5) + " ");
	}
	System.out.println();
	System.out.println("-------------------------------------------------------------------------------------------------------");
	
	for(int i = 0; i < n; ++i) {
	    System.out.print(normalizeLength(getBoundaryName(i), 5) + " : ");
	    for(int j = 0; j < n; ++j) {
		int g = getGluingResult(i, j);
		String s = g == -1 ? "  -  " : normalizeLength(getBoundaryName(g), 5);
		System.out.print(s + " ");
	    }
	    System.out.println();
	}
	
	System.out.println();
	System.out.println("SIGNATURE COMPUTER SIZE");
	System.out.print("     " + " | ");
	for(int i = 0; i < n; ++i) {
	    System.out.print(normalizeLength(getBoundaryName(i), 5) + " ");
	}
	System.out.println();
	System.out.println("-------------------------------------------------------------------------------------------------------");
	
	for(int i = 0; i < n; ++i) {
	    System.out.print(normalizeLength(getBoundaryName(i), 5) + " : ");
	    for(int j = 0; j < n; ++j) {
		
		String s;
		if(canGlue(i, j)) {
		    s = "" + getSignatureComputer(i, j).totalSize;
		} else {
		    s = "  -  ";
		}
		s = normalizeLength(s, 5);	
		System.out.print(s + " ");
	    }
	    System.out.println();
	}	
    }   
}
