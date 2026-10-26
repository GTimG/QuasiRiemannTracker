import type { Page } from "@playwright/test";
import { catalogue } from "../fixtures/catalogue.mjs";

export {
  catalogue,
  record,
  historicalRecord,
  algebraicRecord,
} from "../fixtures/catalogue.mjs";

export async function routeCatalogue(page: Page, data = catalogue()) {
  // Fixture contributions are dated in 2030. Keep the viewing time fixed too,
  // so navigation and reload comparisons do not depend on the wall clock.
  await page.clock.setFixedTime(new Date("2030-10-12T12:00:00Z"));
  await page.route("**/catalogue.json", (route) =>
    route.fulfill({ json: data }),
  );
}
