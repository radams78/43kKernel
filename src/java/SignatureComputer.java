import java.util.*;

/*
 *
 * @inv totalSize is sum of lengths of members of plusZero and plusOne */
public class SignatureComputer {

    private BoundaryGarden myGarden;
    
    private final int N, topBoundaryID, bottomBoundaryID, outerBoundaryID;
    
    private ArrayList<ArrayList<Pair<Integer, Integer> > > plusZero, plusOne;
    
    private ArrayList<InputPair> topInputs, bottomInputs, outerInputs;
    
    public int totalSize;
    
    private String name;
    
    SignatureComputer(BoundaryGarden garden, int topID, int bottomID, String name) {
	this.myGarden = garden;
	this.topBoundaryID = topID;
	this.bottomBoundaryID = bottomID;
	this.outerBoundaryID = myGarden.getGluingResult(topBoundaryID, bottomBoundaryID);
	this.N = myGarden.getAllInputs(outerBoundaryID).size();
	
	this.topInputs = myGarden.getAllInputs(topBoundaryID);
	this.bottomInputs = myGarden.getAllInputs(bottomBoundaryID);
	this.outerInputs = myGarden.getAllInputs(outerBoundaryID);
	this.totalSize = 0;

	DoubleBoundary DB = new DoubleBoundary(myGarden.getBoundary(topBoundaryID), myGarden.getBoundary(bottomBoundaryID));
	totalSize += setPlusB(plusZero, DB, false);
	totalSize += setPlusB(plusOne, DB, true);

	this.name = name;
    }
    
    private int setPlusB(ArrayList<ArrayList<Pair<Integer, Integer>>> plusB, DoubleBoundary DB, boolean X) {
	int size = 0;
	plusB = new ArrayList<ArrayList<Pair<Integer, Integer>>>();
	for (int i = 0; i < N; i++) plusB.add(new ArrayList<Pair<Integer, Integer>>());
	for (int i = 0; i < N; ++i) {
	    InputPair outerInp = outerInputs.get(i);
	    for (Pair<InputPair, InputPair> inpPair : DB.allInputPairsMaybeX(X, outerInp)) {
		InputPair topInp = inpPair.first;
		InputPair bottomInp = inpPair.second;
	    
		int topInpIndex = topInputs.indexOf(topInp);
		int bottomInpIndex = bottomInputs.indexOf(bottomInp);
	    
		// To compute the outer boundary input #i we need top input #topInpIndex and
		// bottom input #bottomInpIndex.
		plusB.get(i).add(new Pair<Integer, Integer> (topInpIndex, bottomInpIndex));
		size++;
	    }
	}
	return size;
    }

    /*    private DoubleBoundary doubleBoundary() {
	return new DoubleBoundary(myGarden.getBoundary(topBoundaryID), myGarden.getBoundary(bottomBoundaryID), name + "_double");
	} */
    
    // COMPUTE PLUS ZERO
    /*    private void setPlusZero() {
	plusZero = new ArrayList<ArrayList<Pair<Integer, Integer> > > ();
	for(int i = 0; i < N; ++i) plusZero.add(new ArrayList<Pair<Integer, Integer> > ());
	
	DoubleBoundary DB = doubleBoundary();
	for(int i = 0; i < N; ++i) {
	    InputPair outerInp = outerInputs.get(i);
	    // NO X!
	    addPairs(DB.allInputPairsNoX(outerInp), plusZero.get(i));
	    	    for(Pair<InputPair, InputPair> inpPair : DB.allInputPairsNoX(outerInp)) {
		InputPair topInp = inpPair.first;
		InputPair bottomInp = inpPair.second;
		
		int topInpIndex = topInputs.indexOf(topInp);
		int bottomInpIndex = bottomInputs.indexOf(bottomInp);
		
		// To compute the outer boundary input #i we need top input #topInpIndex and
		// bottom input #bottomInpIndex.
		plusZero.get(i).add(new Pair<Integer, Integer> (topInpIndex, bottomInpIndex));
		totalSize++;
		} 
	}
    }
    
    // COMPUTE PLUS ONE
    private void setPlusOne() {
	plusOne = new ArrayList<ArrayList<Pair<Integer, Integer> > > ();
	for(int i = 0; i < N; ++i) plusOne.add(new ArrayList<Pair<Integer, Integer> > ());
	
	DoubleBoundary DB = doubleBoundary();
	for(int i = 0; i < N; ++i) {
	    InputPair outerInp = outerInputs.get(i);
	    addPairs(DB.allInputPairsWithX(outerInp), plusOne.get(i));
	    // WITH X!
	     	    for(Pair<InputPair, InputPair> inpPair : DB.allInputPairsWithX(outerInp)) {
		InputPair topInp = inpPair.first;
		InputPair bottomInp = inpPair.second;
		
		int topInpIndex = topInputs.indexOf(topInp);
		int bottomInpIndex = bottomInputs.indexOf(bottomInp);
		
		// To compute the outer boundary input #i we need top input #topInpIndex and
		// bottom input #bottomInpIndex.
		plusOne.get(i).add(new Pair<Integer, Integer> (topInpIndex, bottomInpIndex));
		totalSize++;
		} 
	}
	} */
    
    /*
     * Given the signature of the top and bottom region, compute the signature of the outer region
     */
    public Signature outerSignature(Signature topSignature, Signature bottomSignature) {
	ArrayList<Integer> outerSig = new ArrayList<Integer> ();
	for(int pos = 0; pos < N; ++pos) {
	    
	    // COMPUTE THE SIGNATURE AT POSITION POS.
	    int val = 2;
	    for(Pair<Integer, Integer> pointer : plusZero.get(pos)) {
		int pointerVal = topSignature.get(pointer.first) + bottomSignature.get(pointer.second);
		val = val < pointerVal ? val : pointerVal;
	    }
	    
	    if(val == 2) {
		for(Pair<Integer, Integer> pointer : plusOne.get(pos)) {
		    int pointerVal = topSignature.get(pointer.first) + bottomSignature.get(pointer.second) + 1;
		    val = val < pointerVal ? val : pointerVal;
		}
	    }
	    
	    outerSig.add(val);
	}
	
	return new Signature (outerSig);
    }
    
}
