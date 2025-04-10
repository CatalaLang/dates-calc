package catala.dates_calc;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

public class DatesCalcTest {

    // Helper to read CSV data, using relative path from lib_java
    private static List<String[]> readCsv(String relativePath) throws IOException {
        List<String[]> records = new ArrayList<>();
        // Construct path relative to the lib_java directory (where mvn test runs)
        // Goes up one level to project root, then into test directory
        String filePath = Paths.get("..", "test", relativePath).toString();
        try (BufferedReader br = new BufferedReader(new FileReader(filePath))) {
            String line;
            br.readLine(); // Skip header
            while ((line = br.readLine()) != null) {
                String[] values = line.split(";");
                for (int i = 0; i < values.length; i++) {
                    values[i] = values[i].trim(); // Trim whitespace
                }
                records.add(values);
            }
        }
        return records;
    }

    // --- Data Providers ---
    // Return Stream<Arguments> where each Arguments contains the individual elements of a row
    static Stream<Arguments> exactComputationsProvider() throws IOException {
        // Map each String[] row to Arguments.of(row[0], row[1], row[2])
        return readCsv("exact_computations.csv").stream().map(row -> Arguments.of(row[0], row[1], row[2]));
    }

    static Stream<Arguments> ambiguousComputationsProvider() throws IOException {
        // Map each String[] row to Arguments.of(row[0], row[1], row[2], row[3])
        return readCsv("ambiguous_computations.csv").stream().map(row -> Arguments.of(row[0], row[1], row[2], row[3]));
    }

    static Stream<Arguments> firstLastDayOfMonthProvider() throws IOException {
        // Map each String[] row to Arguments.of(row[0], row[1], row[2])
        return readCsv("first_last_day_of_month.csv").stream().map(row -> Arguments.of(row[0], row[1], row[2]));
    }

    // --- Test Methods ---
    @ParameterizedTest(name = "[{index}] {0} + {1} = {2}")
    @MethodSource("exactComputationsProvider")
    void testAddDatesExact(String dateStr, String periodStr, String expectedDateStr) {
        Date d = Date.fromString(dateStr);
        Period p = Period.fromString(periodStr);
        Date expected = Date.fromString(expectedDateStr);

        assertEquals(expected, d.add(p), "Exact addition (AbortOnRound) failed for " + dateStr + " + " + periodStr);
        assertEquals(expected, d.add(p, Date.Rounding.ROUND_UP), "Exact addition (RoundUp) failed for " + dateStr + " + " + periodStr);
        assertEquals(expected, d.add(p, Date.Rounding.ROUND_DOWN), "Exact addition (RoundDown) failed for " + dateStr + " + " + periodStr);
    }

    @ParameterizedTest(name = "[{index}] {0} + {1} -> UP={2}, DOWN={3}")
    @MethodSource("ambiguousComputationsProvider")
    void testAddDatesAmbiguous(String dateStr, String periodStr, String expectedUpStr, String expectedDownStr) {
        // No need to access via index anymore
        Date d = Date.fromString(dateStr);
        Period p = Period.fromString(periodStr);
        Date expectedUp = Date.fromString(expectedUpStr);
        Date expectedDown = Date.fromString(expectedDownStr);

        assertThrows(AmbiguousComputationException.class, () -> d.add(p), "Ambiguous addition should throw for " + dateStr + " + " + periodStr);
        assertEquals(expectedUp, d.add(p, Date.Rounding.ROUND_UP), "Ambiguous addition (RoundUp) failed for " + dateStr + " + " + periodStr);
        assertEquals(expectedDown, d.add(p, Date.Rounding.ROUND_DOWN), "Ambiguous addition (RoundDown) failed for " + dateStr + " + " + periodStr);
    }

    @ParameterizedTest(name = "[{index}] {0} -> First={1}, Last={2}")
    @MethodSource("firstLastDayOfMonthProvider")
    void testFirstLastDayOfMonth(String dateStr, String expectedFirstStr, String expectedLastStr) {
        Date d = Date.fromString(dateStr);
        Date expectedFirst = Date.fromString(expectedFirstStr);
        Date expectedLast = Date.fromString(expectedLastStr);

        assertEquals(expectedFirst, d.firstDayOfMonth(), "First day of month calculation failed for " + dateStr);
        assertEquals(expectedLast, d.lastDayOfMonth(), "Last day of month calculation failed for " + dateStr);
    }
}
