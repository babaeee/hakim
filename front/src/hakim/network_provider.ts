export const hakimQueryImpl = async (json_obj: any): Promise<any> => {
  return (
    await fetch("http://127.0.0.1:9438/", {
      headers: {
        Accept: "application/json",
        "Content-Type": "application/json",
      },
      method: "POST",
      body: JSON.stringify(json_obj),
    })
  ).json();
};
