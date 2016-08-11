import java.io.*;
import java.util.*;

public class BasicRegionTest{
    static final String OUTPUT_FILE = "BasicRegionTest.v";
    static final String[] IMPORTS = {"BasicRegion", "Boundary", "Region", "Vector"}; 
    static final BasicRegion testBasicRegion = new BasicRegion(BoundaryGardenTest.testGarden, 0, InternalType.isolated, InternalType.top, true, false);
    static final String NAME = "testBasicRegion";

    public static void main(String[] args) throws FileNotFoundException {
	CoqObjectTest.testObject(args[0], OUTPUT_FILE, IMPORTS, testBasicRegion, NAME);
    }
}
