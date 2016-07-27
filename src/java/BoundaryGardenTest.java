import java.util.*;

public class BoundaryGardenTest {
    public static final Boundary[] boundaries = { BoundaryTest.testBoundary };
    public static final BoundaryGarden testGarden = new BoundaryGarden(new ArrayList<Boundary>(Arrays.asList(boundaries)),
								       new ArrayList<String>(Arrays.asList("testBoundary")));
}
