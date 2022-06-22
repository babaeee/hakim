// @ts-nocheck

import puppeteer, { Page } from "puppeteer";

test('Hello world', () => {
    expect(2 + 2).toBe(4);
});

const clickOnText = async (page: Page, txt: string) => {
    const [button] = await page.$x(`//a[contains(., '${txt}')] | //button[contains(., '${txt}')]`);
    await button.click();
};

const assertTextExists = async (page: Page, txt: string) => {
    const x = await page.$x(`//*[contains(., '${txt}')]`);
    expect(x.length).toBeGreaterThan(0);
};

test('Hello puppeteer', async () => {
    const browser = await puppeteer.launch();
    const page = await browser.newPage();
    await page.goto('http://127.0.0.1:4000', {
        waitUntil: 'networkidle0',
    });
    expect(await page.title()).toBe("اثبات چک کن ببعییی - صفحه اصلی");
    await browser.close()
});

test('Sandbox mode simple', async () => {
    const browser = await puppeteer.launch();
    const page = await browser.newPage();
    await page.goto('http://127.0.0.1:4000', {
        waitUntil: 'networkidle0',
    });
    await clickOnText(page, 'جعبه شنی');
    await page.type('input', '2+2=4');
    await clickOnText(page, 'ارسال');
    await clickOnText(page, 'اثبات خودکار');
    await assertTextExists(page, 'هدف دیگری برای اثبات وجود');
    await browser.close()
});
