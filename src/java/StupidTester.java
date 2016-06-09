import java.io.*;
import java.util.*;

public class StupidTester {
	
	public static ArrayList<BitSet> getJohanSig (String filename) {
		System.out.println("Reading johan signatues from file ...");
		ArrayList<SignatureTranscript> merged = SignatureTranscript.readListFromFile(filename, true);
		System.out.println("Done.");
		ArrayList<BitSet> ans = new ArrayList<BitSet> ();
		for(SignatureTranscript t : merged) ans.add((new Signature(t.sig)).store());
		return ans;
	}
	

	public static ArrayList<BitSet> getAllJohanSig (String filename) {
		System.out.println("Reading johan signatues from file ...");
		ArrayList<SignatureTranscript> merged = SignatureTranscript.readListFromFile(filename, true);
		System.out.println("Done.");
		ArrayList<BitSet> ans = new ArrayList<BitSet> ();
		for(SignatureTranscript t : merged) ans.add((new Signature(t.sig)).store());
		return ans;
	}

	public static SignatureTranscript getJohanSig (String filename, int i) {
		System.out.println("Reading johan signatues from file ...");
		ArrayList<SignatureTranscript> merged = SignatureTranscript.readListFromFile(filename, i + 5, true);
		System.out.println("Done.");
		return merged.get(i);	
	}
	
	public static Region getDanielRegion (String boundaryName, int nr) throws Exception {
		DistinctSignatureEnumerator DSE = new DistinctSignatureEnumerator("boundaries.txt");
		ArrayList<Region> allReg = DSE.allSignatureMinimalRegionsOfBoundaryType(boundaryName);
		return allReg.get(nr);
	}
	

	// Find the first signature that I have that other guy does not.
	public static void computeMissingSig(String myName, String otherGuyName, ArrayList<BitSet> myList, HashSet<BitSet> otherGuysSet) {
		for(int i = 0; i < myList.size(); ++i) {
			if(!otherGuysSet.contains(myList.get(i))) {
				System.out.println(otherGuyName + " misses " + myName + "'s signature number " + i);
				return;
			}
		}
		System.out.println(otherGuyName + " has all " + myName + "'s signatures!");
	}

	public static HashSet<BitSet> signatureSetFromRegionList (ArrayList<Region> l) {
		return new HashSet<BitSet> (signatureListFromRegionList(l));
	}
	
	public static ArrayList<BitSet> signatureListFromRegionList (ArrayList<Region> l) {
		ArrayList<BitSet> ans = new ArrayList<BitSet> ();
		for(Region r : l) ans.add(r.getSignature().store());
		return ans;
	}
	
	public static HashMap<BitSet, Integer> signatureMapFromRegionList (ArrayList<Region> l) {
		HashMap<BitSet, Integer> ans = new HashMap<BitSet, Integer> ();
		for(Region r : l) ans.put(r.getSignature().store(), r.size);
		return ans;
	}
	
	public static ArrayList<Integer> readSizeList(String filename) {
		Scanner sc = new Scanner("dummy");
	
		try {
			sc = new Scanner(new File(filename));
		} catch(Exception e) {
			System.out.println("Shit went wrong when reading from file");
			System.out.println(e);
			System.exit(1);
		}
	
		ArrayList<Integer> ans = new ArrayList<Integer> ();
		while(sc.hasNext()) ans.add(sc.nextInt());
		sc.close();
		return ans;
	}
	
	public static HashMap<BitSet, Integer> makeMap(ArrayList<BitSet> keys, ArrayList<Integer> values) {
		HashMap<BitSet, Integer> ans = new HashMap<BitSet, Integer> ();
		for(int i = 0; i < keys.size(); ++i) ans.put(keys.get(i), values.get(i));
		return ans;
	}
	
	
	
	public static void johanDanielCompare() throws Exception {
		ArrayList<BitSet> johanSig22 = getAllJohanSig("johanSigTrans22.txt");
		ArrayList<BitSet> johanSig21 = getAllJohanSig("johanSigTrans21.txt");
		ArrayList<BitSet> johanSig20 = getAllJohanSig("johanSigTrans20.txt");
		ArrayList<BitSet> johanSig11 = getAllJohanSig("johanSigTrans11.txt");
		ArrayList<BitSet> johanSig10 = getAllJohanSig("johanSigTrans10.txt");
		
		ArrayList<Integer> johanSize22 = readSizeList("size22.txt");
		ArrayList<Integer> johanSize21 = readSizeList("size21.txt");
		ArrayList<Integer> johanSize20 = readSizeList("size20.txt");
		ArrayList<Integer> johanSize11 = readSizeList("size11.txt");
		ArrayList<Integer> johanSize10 = readSizeList("size10.txt");
		
		HashMap<BitSet, Integer> johanMap22 = makeMap(johanSig22, johanSize22);
		HashMap<BitSet, Integer> johanMap21 = makeMap(johanSig21, johanSize21);
		HashMap<BitSet, Integer> johanMap20 = makeMap(johanSig20, johanSize20);
		HashMap<BitSet, Integer> johanMap11 = makeMap(johanSig11, johanSize11);
		HashMap<BitSet, Integer> johanMap10 = makeMap(johanSig10, johanSize10);
		
		DistinctSignatureEnumerator DSE = new DistinctSignatureEnumerator("boundaries.txt");
		ArrayList<Region> allType22 = DSE.allSignatureMinimalRegionsOfBoundaryType("T22");
		ArrayList<Region> allType21 = DSE.allSignatureMinimalRegionsOfBoundaryType("T21");
		ArrayList<Region> allType20 = DSE.allSignatureMinimalRegionsOfBoundaryType("T20");
		ArrayList<Region> allType11 = DSE.allSignatureMinimalRegionsOfBoundaryType("T11");
		ArrayList<Region> allType10 = DSE.allSignatureMinimalRegionsOfBoundaryType("T10");
	
		HashMap<BitSet, Integer> danielMap22 = signatureMapFromRegionList(allType22);
		HashMap<BitSet, Integer> danielMap21 = signatureMapFromRegionList(allType21);
		HashMap<BitSet, Integer> danielMap20 = signatureMapFromRegionList(allType20);
		HashMap<BitSet, Integer> danielMap11 = signatureMapFromRegionList(allType11);
		HashMap<BitSet, Integer> danielMap10 = signatureMapFromRegionList(allType10);
		
		
		System.out.println("22:" + johanMap22.equals(danielMap22));
		System.out.println("21:" + johanMap21.equals(danielMap21));
		System.out.println("20:" + johanMap20.equals(danielMap20));
		System.out.println("11:" + johanMap11.equals(danielMap11));
		System.out.println("10:" + johanMap10.equals(danielMap10));
		
		
	/*	
		
		System.out.println("22:");
		computeMissingSig("Johan", "Daniel", johanSig22, signatureSetFromRegionList(allType22));
		computeMissingSig("Daniel", "Johan", signatureListFromRegionList(allType22), new HashSet<BitSet> (johanSig22));
		
		System.out.println("21:");
		computeMissingSig("Johan", "Daniel", johanSig21, signatureSetFromRegionList(allType21));
		computeMissingSig("Daniel", "Johan", signatureListFromRegionList(allType21), new HashSet<BitSet> (johanSig21));
		
		System.out.println("20:");
		computeMissingSig("Johan", "Daniel", johanSig20, signatureSetFromRegionList(allType20));
		computeMissingSig("Daniel", "Johan", signatureListFromRegionList(allType20), new HashSet<BitSet> (johanSig20));
		
		System.out.println("11:");
		computeMissingSig("Johan", "Daniel", johanSig11, signatureSetFromRegionList(allType11));
		computeMissingSig("Daniel", "Johan", signatureListFromRegionList(allType11), new HashSet<BitSet> (johanSig11));
		
		System.out.println("10:");
		computeMissingSig("Johan", "Daniel", johanSig10, signatureSetFromRegionList(allType10));
		computeMissingSig("Daniel", "Johan", signatureListFromRegionList(allType10), new HashSet<BitSet> (johanSig10));
	*/	
	}
		
	public static void main (String[] args) throws Exception {
		johanDanielCompare();
		//System.out.println(getDanielRegion("T22",7312));
	}
}

//SignatureTranscript r0sig = SignatureTranscript.readFromFile("rs14nr1.txt", true);
//SignatureTranscript r1sig = SignatureTranscript.readFromFile("rs14nr2.txt", true);

//ArrayList<SignatureTranscript> merged = SignatureTranscript.readListFromFile("merged.txt", true);


//System.out.println(mySig.sig);
//System.out.println(johanSig.sig);

/*		for(int i = 0; i < mySig.sig.size(); ++i) {
	if(mySig.sig.get(i) != johanSig.sig.get(i)) {
		System.out.println(mySig.myBoundary.allValidInputs().get(i));
		System.out.println("Daniel: " + mySig.sig.get(i));
		System.out.println("Johan: " + johanSig.sig.get(i));
	}
}
*/
/*		
if(r0sig.equals(merged.get(0)) && r1sig.equals(merged.get(1))) {
	System.out.println("hurra");
} else {
	System.out.println("uffda");
}

/*
if(mySig.sig.equals(johanSig.sig)) {
	System.out.println("hurra");
} else {
	System.out.println("uffda");
}*/

// --------------------------------------------------------------------
/*
 * 		System.out.print("Reading input ...");
		BoundaryListReader BLR = new BoundaryListReader(new Scanner(new File("boundaries.txt")));
		Pair<ArrayList<Boundary>, ArrayList<String> > BL = BLR.readBoundaries();
		BLR.close();
		System.out.println("done.");
		
		System.out.print("Populating Boundary Garden ... ");
		BoundaryGarden myGarden = new BoundaryGarden(BL.first, BL.second);
		System.out.println("done.");
		
		BasicRegion one = new BasicRegion(myGarden, myGarden.getIdOfBoundaryWithName("T21L"), BasicRegion.top, BasicRegion.none, false, false);
		BasicRegion two = new BasicRegion(myGarden, myGarden.getIdOfBoundaryWithName("T10"), BasicRegion.none, BasicRegion.none, false, false);
		BasicRegion three = new BasicRegion(myGarden, myGarden.getIdOfBoundaryWithName("T01"), BasicRegion.none, BasicRegion.none, false, false);
		BasicRegion four = new BasicRegion(myGarden, myGarden.getIdOfBoundaryWithName("T12L"), BasicRegion.none, BasicRegion.none, false, false);

		BasicRegionGenerator genOne = new BasicRegionGenerator(myGarden, myGarden.getIdOfBoundaryWithName("T21L"));
		BasicRegionGenerator genTwo = new BasicRegionGenerator(myGarden, myGarden.getIdOfBoundaryWithName("T10"));
		BasicRegionGenerator genThree = new BasicRegionGenerator(myGarden, myGarden.getIdOfBoundaryWithName("T01"));
		BasicRegionGenerator genFour = new BasicRegionGenerator(myGarden, myGarden.getIdOfBoundaryWithName("T12L"));
		
		if(genOne.getAllBasicRegions().contains(one)) System.out.println("One-hurra");
		else System.out.println("One-uffda");			
		
		if(genTwo.getAllBasicRegions().contains(two)) System.out.println("Two-hurra");
		else System.out.println("Two-uffda");			

		if(genThree.getAllBasicRegions().contains(three)) System.out.println("Three-hurra");
		else System.out.println("Three-uffda");			
		
		if(genFour.getAllBasicRegions().contains(four)) System.out.println("Four-hurra");
		else System.out.println("Four-uffda");			
		
		CompositeRegion oneTwo = new CompositeRegion(myGarden, one, two);
		CompositeRegion oneTwoThree = new CompositeRegion(myGarden, oneTwo, three);
		CompositeRegion finalRegion = new CompositeRegion(myGarden, oneTwoThree, four);

//		System.out.println(one);
//		System.out.println(one.getSignatureTranscript());
		
//		BasicRegion normalR = new BasicRegion(myGarden, myGarden.getIdOfBoundaryWithName("T22"), BasicRegion.top, BasicRegion.none, false, false);
//		System.out.println(normalR);
//		System.out.println(normalR.getSignatureTranscript());
		
		
		
		
		SignatureTranscript finalTrans = finalRegion.getSignatureTranscript();
		SignatureTranscript johanTrans = getJohanSig(10);
		
		finalTrans.compareWith(johanTrans);

*/
